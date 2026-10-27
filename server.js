// 우리끼리 홀덤 — 실시간 서버
// 실행: npm start  (외부 패키지 없음. PORT 환경변수가 있으면 그 포트 사용)
// 서버 → 화면: Server-Sent Events(/events), 화면 → 서버: POST /api
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = process.env.PORT || 3000;
const PAGE = fs.readFileSync(path.join(__dirname, 'index.html'));


/* ---------------- 카드 & 족보 ---------------- */
const RANKS = '23456789TJQKA', SUITS = 'shdc';
const randInt = n => crypto.randomInt(n);
function newDeck() {
  const d = [];
  for (const r of RANKS) for (const s of SUITS) d.push(r + s);
  for (let i = d.length - 1; i > 0; i--) { const j = randInt(i + 1); [d[i], d[j]] = [d[j], d[i]]; }
  return d;
}
function eval5(cs) {
  const rs = cs.map(c => RANKS.indexOf(c[0])).sort((a, b) => b - a);
  const flush = cs.every(c => c[1] === cs[0][1]);
  const uniq = [...new Set(rs)];
  let sh = -1;
  if (uniq.length === 5) { if (uniq[0] - uniq[4] === 4) sh = uniq[0]; else if (uniq[0] === 12 && uniq[1] === 3) sh = 3; }
  const cnt = {}; rs.forEach(r => cnt[r] = (cnt[r] || 0) + 1);
  const g = Object.entries(cnt).map(([r, c]) => [+r, c]).sort((a, b) => b[1] - a[1] || b[0] - a[0]);
  const gr = g.map(x => x[0]);
  if (sh >= 0 && flush) return [8, sh];
  if (g[0][1] === 4) return [7, ...gr];
  if (g[0][1] === 3 && g[1][1] === 2) return [6, ...gr];
  if (flush) return [5, ...rs];
  if (sh >= 0) return [4, sh];
  if (g[0][1] === 3) return [3, ...gr];
  if (g[0][1] === 2 && g[1][1] === 2) return [2, ...gr];
  if (g[0][1] === 2) return [1, ...gr];
  return [0, ...rs];
}
function cmpScore(a, b) { for (let i = 0; i < Math.max(a.length, b.length); i++) { const d = (a[i] ?? -1) - (b[i] ?? -1); if (d) return d; } return 0; }
function bestHand(cards) {
  let best = null; const n = cards.length;
  const pick = (start, acc) => {
    if (acc.length === 5) { const s = eval5(acc); if (!best || cmpScore(s, best) > 0) best = s; return; }
    for (let i = start; i <= n - (5 - acc.length); i++) pick(i + 1, [...acc, cards[i]]);
  };
  pick(0, []); return best;
}
const RN = r => r === 8 ? '10' : RANKS[r];
function handName(s) {
  switch (s[0]) {
    case 8: return s[1] === 12 ? '로열 플러시' : `${RN(s[1])} 스트레이트 플러시`;
    case 7: return `${RN(s[1])} 포카드`;
    case 6: return `${RN(s[1])} 풀하우스`;
    case 5: return `${RN(s[1])} 하이 플러시`;
    case 4: return `${RN(s[1])} 하이 스트레이트`;
    case 3: return `${RN(s[1])} 트리플`;
    case 2: return `${RN(s[1])}·${RN(s[2])} 투페어`;
    case 1: return `${RN(s[1])} 원페어`;
    default: return `${RN(s[1])} 하이`;
  }
}
const fmt = n => Number(n || 0).toLocaleString('ko-KR');
const BETTING = new Set(['pre', 'flop', 'turn', 'river']);
const CODE_ABC = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';

/* ---------------- 방 ---------------- */
const rooms = new Map();

class Room {
  constructor(code) {
    this.code = code;
    this.created = Date.now();
    this.hostPid = null;
    this.settings = { stack: 1000, sb: 10, bb: 20, timer: 30 };
    this.status = 'lobby';
    this.seats = [];
    this.hand = this.blankHand(0);
    this.chat = [];
    this.chatI = 0;
    this.socks = new Set();
    this.msg = '';
    this.champ = '';
    this.turnStart = 0; this.runoutAt = 0; this.nextAt = 0;
    this.emptySince = Date.now();
    this.dirty = false;
  }
  blankHand(sq) { return { no: 0, d: -1, sq, tu: -1, st: 'idle', bd: [], pot: 0, cb: 0, mr: 0, holes: {}, deck: [], res: '', sbI: -1, bbI: -1 }; }
  newSeat(pid, name) {
    return { pid, id: crypto.randomBytes(4).toString('hex'), name, stack: this.settings.stack, bet: 0, contrib: 0, folded: false, allIn: false, acted: false, inHand: false, out: false, online: true, offSince: 0, shown: null, la: '', won: 0, hn: '' };
  }
  seatOf(pid) { return this.seats.find(s => s.pid === pid); }
  log(t) { this.pushChat({ sys: 1, t }); }
  pushChat(m) {
    m.id = ++this.chatI; m.at = Date.now();
    this.chat.push(m); if (this.chat.length > 60) this.chat.shift();
    for (const c of this.socks) c.emit('chat', m);
  }

  /* ---- 베팅 엔진 ---- */
  needsAct(s) { const hd = this.hand; return s.inHand && !s.folded && !s.allIn && (!s.acted || s.bet < hd.cb); }
  findNeed(start, inclusive) {
    const n = this.seats.length;
    const can = this.seats.filter(s => s.inHand && !s.folded && !s.allIn);
    if (can.length === 1 && can[0].bet >= this.hand.cb) return -1;
    for (let k = inclusive ? 0 : 1; k <= n; k++) { const j = ((start + k) % n + n) % n; if (this.needsAct(this.seats[j])) return j; }
    return -1;
  }
  nextIn(from) { const n = this.seats.length; for (let k = 1; k <= n; k++) { const j = ((from + k) % n + n) % n; if (this.seats[j].inHand) return j; } return -1; }
  pay(s, amt) { const p = Math.max(0, Math.min(amt, s.stack)); s.stack -= p; s.bet += p; s.contrib += p; if (s.stack === 0 && s.inHand && !s.folded) s.allIn = true; return p; }

  startHand() {
    const hd = this.hand;
    const elig = this.seats.map((s, i) => i).filter(i => this.seats[i].stack > 0 && this.seats[i].online);
    this.seats.forEach(s => Object.assign(s, { bet: 0, contrib: 0, folded: false, allIn: false, acted: false, inHand: false, shown: null, la: '', won: 0, hn: '' }));
    if (elig.length < 2) {
      this.status = 'playing'; hd.st = 'idle'; hd.tu = -1; hd.bd = []; hd.pot = 0; hd.res = '';
      this.msg = '칩이 있는 플레이어가 2명 이상 접속해야 다음 핸드를 시작해요';
      hd.sq++; this.nextAt = Date.now() + 3000; this.dirty = true; return;
    }
    this.msg = '';
    elig.forEach(i => this.seats[i].inHand = true);
    hd.no++;
    hd.d = this.nextIn(hd.d ?? -1);
    let sbI, bbI;
    if (elig.length === 2) { sbI = hd.d; bbI = this.nextIn(hd.d); } else { sbI = this.nextIn(hd.d); bbI = this.nextIn(sbI); }
    this.pay(this.seats[sbI], this.settings.sb); this.seats[sbI].la = 'SB';
    this.pay(this.seats[bbI], this.settings.bb); this.seats[bbI].la = 'BB';
    Object.assign(hd, { sbI, bbI, cb: this.settings.bb, mr: this.settings.bb, pot: 0, bd: [], st: 'pre', res: '', deck: newDeck(), holes: {} });
    for (let r = 0; r < 2; r++) { let j = hd.d; for (let c = 0; c < elig.length; c++) { j = this.nextIn(j); const pid = this.seats[j].pid; (hd.holes[pid] || (hd.holes[pid] = [])).push(hd.deck.pop()); } }
    this.status = 'playing';
    const first = elig.length === 2 ? sbI : this.nextIn(bbI);
    hd.tu = this.findNeed(first, true); hd.sq++; this.turnStart = Date.now();
    this.log(`#${hd.no} 핸드 시작 · 딜러 ${this.seats[hd.d].name}`);
    if (hd.tu < 0) this.runoutAt = Date.now() + 900;
    this.dirty = true;
  }
  act(i, a, amt) {
    const hd = this.hand, s = this.seats[i];
    if (!s || hd.tu !== i || !BETTING.has(hd.st)) return false;
    const toCall = hd.cb - s.bet;
    if (a === 'fold') { s.folded = true; s.la = '폴드'; }
    else if (a === 'check') { if (toCall > 0) return false; s.la = '체크'; }
    else if (a === 'call') { if (toCall <= 0) s.la = '체크'; else { this.pay(s, toCall); s.la = s.stack === 0 ? '올인' : '콜'; } }
    else if (a === 'raise' || a === 'allin') {
      const maxT = s.bet + s.stack;
      let target = a === 'allin' ? maxT : Math.floor(Number(amt) || 0);
      if (target > maxT) target = maxT;
      if (target <= hd.cb || s.acted) { if (a === 'allin') return this.act(i, 'call'); return false; }
      const others = this.seats.filter((o, k) => k !== i && o.inHand && !o.folded && !o.allIn).length;
      if (!others) return this.act(i, 'call');
      const minT = hd.cb + hd.mr;
      if (target < minT && target < maxT) target = Math.min(minT, maxT);
      const raiseBy = target - hd.cb, wasZero = hd.cb === 0;
      this.pay(s, target - s.bet);
      if (raiseBy >= hd.mr) { hd.mr = raiseBy; this.seats.forEach((o, k) => { if (k !== i && o.inHand && !o.folded && !o.allIn) o.acted = false; }); }
      hd.cb = target;
      s.la = s.stack === 0 ? '올인' : (wasZero ? '벳 ' : '레이즈 ') + fmt(target);
    } else return false;
    s.acted = true;
    const live = this.seats.filter(o => o.inHand && !o.folded);
    if (live.length === 1) { this.winByFold(live[0]); return true; }
    const nt = this.findNeed(i, false);
    if (nt < 0) this.endStreet(); else { hd.tu = nt; hd.sq++; this.turnStart = Date.now(); this.dirty = true; }
    return true;
  }
  endStreet() {
    const hd = this.hand;
    this.seats.forEach(o => { hd.pot += o.bet; o.bet = 0; o.acted = false; if (o.inHand && !o.folded && o.la !== '올인') o.la = ''; });
    hd.cb = 0; hd.mr = this.settings.bb;
    if (hd.st === 'river') { this.showdown(); return; }
    const can = this.seats.filter(o => o.inHand && !o.folded && !o.allIn);
    const runout = can.length <= 1;
    if (runout) this.seats.forEach(o => { if (o.inHand && !o.folded) o.shown = hd.holes[o.pid]; });
    hd.deck.pop(); // 번
    if (hd.st === 'pre') { hd.bd = [hd.deck.pop(), hd.deck.pop(), hd.deck.pop()]; hd.st = 'flop'; }
    else if (hd.st === 'flop') { hd.bd = [...hd.bd, hd.deck.pop()]; hd.st = 'turn'; }
    else if (hd.st === 'turn') { hd.bd = [...hd.bd, hd.deck.pop()]; hd.st = 'river'; }
    if (runout) { hd.tu = -1; this.runoutAt = Date.now() + 1500; }
    else { hd.tu = this.findNeed(hd.d, false); this.turnStart = Date.now(); if (hd.tu < 0) this.runoutAt = Date.now() + 1500; }
    hd.sq++; this.dirty = true;
  }
  orderFromDealer(s) { const n = this.seats.length; return ((this.seats.indexOf(s) - this.hand.d + n) % n) || n; }
  showdown() {
    const hd = this.hand;
    const all = this.seats.filter(o => o.inHand), cont = all.filter(o => !o.folded);
    const score = new Map();
    cont.forEach(o => { o.shown = hd.holes[o.pid]; const sc = bestHand([...hd.holes[o.pid], ...hd.bd]); score.set(o, sc); o.hn = handName(sc); });
    const levels = [...new Set(all.map(o => o.contrib).filter(x => x > 0))].sort((a, b) => a - b);
    let prev = 0; const wins = new Map();
    for (const L of levels) {
      let amt = 0; all.forEach(o => { amt += Math.min(o.contrib, L) - Math.min(o.contrib, prev); });
      let el = cont.filter(o => o.contrib >= L); if (!el.length) el = cont;
      let best = null; el.forEach(o => { const sc = score.get(o); if (!best || cmpScore(sc, best) > 0) best = sc; });
      const w = el.filter(o => cmpScore(score.get(o), best) === 0).sort((a, b) => this.orderFromDealer(a) - this.orderFromDealer(b));
      const share = Math.floor(amt / w.length); let rem = amt - share * w.length;
      w.forEach(o => { const x = share + (rem > 0 ? 1 : 0); if (rem > 0) rem--; wins.set(o, (wins.get(o) || 0) + x); });
      prev = L;
    }
    const parts = [];
    wins.forEach((x, o) => { o.stack += x; o.won = x; parts.push(`${o.name} +${fmt(x)}`); });
    const top = [...wins.keys()].sort((a, b) => b.won - a.won)[0];
    hd.res = top ? `${[...wins.keys()].map(o => o.name).join(', ')} 승리 · ${top.hn}` : '';
    this.log(`#${hd.no} 쇼다운 · ${parts.join(', ')}${top ? ' (' + top.hn + ')' : ''}`);
    hd.st = 'show'; hd.tu = -1; hd.sq++; this.endHand();
  }
  winByFold(w) {
    const hd = this.hand;
    let total = hd.pot; this.seats.forEach(o => { total += o.bet; o.bet = 0; });
    hd.pot = total; w.stack += total; w.won = total;
    hd.res = `${w.name} 승리 · 모두 폴드`;
    this.log(`#${hd.no} ${w.name} +${fmt(total)} (모두 폴드)`);
    hd.st = 'show'; hd.tu = -1; hd.sq++; this.endHand();
  }
  endHand() {
    this.seats.forEach(o => { if (o.stack <= 0) o.out = true; });
    const alive = this.seats.filter(o => o.stack > 0);
    if (alive.length < 2) { this.status = 'over'; this.champ = alive[0] ? alive[0].name : ''; this.log(`게임 종료 · ${this.champ} 우승`); this.nextAt = 0; }
    else this.nextAt = Date.now() + 7000;
    this.dirty = true;
  }

  /* ---- 방장 명령 ---- */
  hostCmd(cmd, arg) {
    if (cmd === 'set' && this.status === 'lobby' && arg && typeof arg === 'object') {
      const ok = { stack: [500, 1000, 2000, 5000, 10000], sb: [5, 10, 25, 50, 100], bb: [10, 20, 50, 100, 200], timer: [20, 30, 60, 0] };
      for (const k of Object.keys(ok)) if (arg[k] !== undefined && ok[k].includes(+arg[k])) this.settings[k] = +arg[k];
      this.seats.forEach(s => { s.stack = this.settings.stack; });
      this.dirty = true;
    } else if (cmd === 'start' && this.status === 'lobby') {
      if (this.seats.filter(s => s.online).length < 2) return '2명 이상 있어야 시작할 수 있어요';
      this.seats.forEach(s => Object.assign(s, { stack: this.settings.stack, out: false }));
      this.hand = this.blankHand(this.hand.sq + 1); this.champ = '';
      this.log(`게임 시작 · 시작 칩 ${fmt(this.settings.stack)}, 블라인드 ${this.settings.sb}/${this.settings.bb}`);
      this.startHand();
    } else if (cmd === 'next' && this.status === 'playing' && (this.hand.st === 'show' || this.hand.st === 'idle')) {
      this.nextAt = 0; this.startHand();
    } else if (cmd === 'rebuy') {
      let k = 0; this.seats.forEach(s => { if (s.out && !s.inHand) { s.stack = this.settings.stack; s.out = false; k++; } });
      if (k) { this.log(`탈락자 ${k}명 리바이 (${fmt(this.settings.stack)})`); this.dirty = true; }
    } else if (cmd === 'lobby') {
      this.status = 'lobby'; this.nextAt = 0; this.runoutAt = 0;
      this.hand = this.blankHand(this.hand.sq + 1); this.champ = ''; this.msg = '';
      this.seats = this.seats.filter(s => s.online);
      this.seats.forEach(s => Object.assign(s, { stack: this.settings.stack, bet: 0, contrib: 0, folded: false, allIn: false, acted: false, inHand: false, out: false, shown: null, la: '', won: 0, hn: '' }));
      this.log('대기실로 돌아왔어요'); this.dirty = true;
    }
    return '';
  }

  /* ---- 주기 처리 ---- */
  tick(now) {
    // 방장이 30초 이상 접속이 끊기면 다음 사람에게 방장 넘기기
    const host = this.seatOf(this.hostPid);
    if (!host || (!host.online && now - host.offSince > 30000)) {
      const next = this.seats.find(s => s.online && s.pid !== this.hostPid);
      if (next) { this.hostPid = next.pid; this.log(`${next.name}님이 새 방장이 됐어요`); this.dirty = true; }
    }
    // 대기실에서 60초 넘게 끊긴 사람은 자리 정리
    if (this.status !== 'playing') {
      const before = this.seats.length;
      this.seats = this.seats.filter(s => { if (s.online || now - s.offSince < 60000) return true; this.log(`${s.name} 퇴장`); return false; });
      if (before !== this.seats.length) this.dirty = true;
    }
    if (this.status === 'playing') {
      const hd = this.hand;
      if (this.runoutAt && now >= this.runoutAt) { this.runoutAt = 0; this.endStreet(); }
      else if (this.nextAt && now >= this.nextAt) { this.nextAt = 0; this.startHand(); }
      else if (hd.tu >= 0 && BETTING.has(hd.st)) {
        const s = this.seats[hd.tu];
        const lim = !s.online ? 8000 : (this.settings.timer ? this.settings.timer * 1000 : Infinity);
        if (now - this.turnStart > lim) { this.log(`${s.name} 시간 초과`); this.act(hd.tu, hd.cb > s.bet ? 'fold' : 'check'); }
      }
    }
    if (this.dirty) { this.dirty = false; this.broadcast(); }
  }

  /* ---- 화면에 보낼 상태 ---- */
  publicState() {
    const hd = this.hand;
    return {
      code: this.code, status: this.status, set: this.settings, msg: this.msg, champ: this.champ,
      seats: this.seats.map(s => ({ id: s.id, n: s.name, s: s.stack, b: s.bet, f: s.folded ? 1 : 0, a: s.allIn ? 1 : 0, ac: s.acted ? 1 : 0, ih: s.inHand ? 1 : 0, o: s.out ? 1 : 0, aw: s.online ? 0 : 1, sh: s.shown || 0, la: s.la, w: s.won, hn: s.hn, host: s.pid === this.hostPid ? 1 : 0 })),
      h: { no: hd.no, d: hd.d, sb: hd.sbI, bb: hd.bbI, st: hd.st, bd: hd.bd, pot: hd.pot, cb: hd.cb, mr: hd.mr, tu: hd.tu, sq: hd.sq, res: hd.res }
    };
  }
  sendTo(sock, pub) {
    const pid = sock.pid;
    const me = this.seats.findIndex(s => s.pid === pid);
    const seat = this.seats[me];
    const hole = seat && seat.inHand ? (this.hand.holes[pid] || null) : null;
    sock.emit('state', { ...pub, me, hole, isHost: pid === this.hostPid });
  }
  broadcast() { const pub = this.publicState(); for (const s of this.socks) this.sendTo(s, pub); }
}

/* ---------------- 접속 처리 ---------------- */
const clean = (v, n) => String(v ?? '').replace(/[\u0000-\u001f\u007f]/g, '').trim().slice(0, n);

/* ---------------- 접속(SSE 스트림) ---------------- */
const clients = new Map(); // pid -> Set<Client>
class Client {
  constructor(pid, res) { this.pid = pid; this.res = res; this.code = null; this.lastChat = 0; this.alive = true; }
  emit(ev, data) {
    if (!this.alive) return;
    try { this.res.write(`event: ${ev}\ndata: ${JSON.stringify(data)}\n\n`); } catch (e) { this.alive = false; }
  }
}
function clientsOf(pid) { return clients.get(pid) || new Set(); }

function leaveCurrent(c) {
  const room = rooms.get(c.code);
  if (!room) { c.code = null; return; }
  room.socks.delete(c);
  const stillHere = [...room.socks].some(s => s.pid === c.pid);
  const seat = room.seatOf(c.pid);
  if (seat && !stillHere) { seat.online = false; seat.offSince = Date.now(); room.dirty = true; }
  if (!room.socks.size) room.emptySince = Date.now();
  c.code = null;
}
function enter(c, room, name) {
  if (c.code && c.code !== room.code) leaveCurrent(c);
  c.code = room.code;
  room.socks.add(c);
  const pid = c.pid;
  let seat = room.seatOf(pid);
  if (seat) {
    seat.online = true;
    if (name && seat.name !== name) seat.name = name;
  } else if (room.seats.length < 8) {
    seat = room.newSeat(pid, name);
    room.seats.push(seat);
    room.log(`${name} 입장${room.status === 'playing' ? ' · 다음 핸드부터 참여' : ''}`);
  }
  if (!room.hostPid) room.hostPid = pid;
  room.dirty = true;
  room.tick(Date.now());
  c.emit('chatlog', room.chat);
  if (!seat) c.emit('err', '자리가 꽉 차서 관전으로 들어왔어요');
}
function roomOf(pid) { for (const c of clientsOf(pid)) { const r = rooms.get(c.code); if (r) return r; } return null; }
function tell(pid, ev, data) { for (const c of clientsOf(pid)) c.emit(ev, data); }

function handle(msg) {
  const pid = clean(msg && msg.pid, 40);
  const cs = clientsOf(pid);
  if (pid.length < 12 || !cs.size) return;
  const type = String(msg.type || '');
  if (type === 'create') {
    const name = clean(msg.name, 10) || '방장';
    let code; do { code = Array.from({ length: 5 }, () => CODE_ABC[randInt(CODE_ABC.length)]).join(''); } while (rooms.has(code));
    const room = new Room(code); rooms.set(code, room);
    room.hostPid = pid;
    room.log(`방이 만들어졌어요. 코드 ${code}`);
    for (const c of cs) enter(c, room, name);
  } else if (type === 'join') {
    const code = clean(msg.code, 5).toUpperCase();
    const name = clean(msg.name, 10) || '손님';
    const room = rooms.get(code);
    if (!room) { tell(pid, 'nojoin', '그 코드의 방이 없어요. 코드를 다시 확인해 주세요'); return; }
    for (const c of cs) enter(c, room, name);
  } else if (type === 'act') {
    const room = roomOf(pid); if (!room || room.status !== 'playing') return;
    const i = room.seats.findIndex(s => s.pid === pid);
    if (i < 0 || room.hand.tu !== i || msg.sq !== room.hand.sq) return;
    if (!room.act(i, String(msg.a), msg.x)) tell(pid, 'err', '지금은 그 액션을 할 수 없어요');
    room.dirty = true; room.tick(Date.now());
  } else if (type === 'chat') {
    const room = roomOf(pid); if (!room) return;
    const c0 = [...cs][0]; const now = Date.now();
    if (now - c0.lastChat < 400) return; c0.lastChat = now;
    const t = clean(msg.t, 140); if (!t) return;
    const seat = room.seatOf(pid);
    room.pushChat({ n: seat ? seat.name : '관전자', sid: seat ? seat.id : '', t });
  } else if (type === 'host') {
    const room = roomOf(pid); if (!room || room.hostPid !== pid) return;
    const err = room.hostCmd(String(msg.cmd), msg.arg);
    if (err) tell(pid, 'err', err);
    room.tick(Date.now());
  } else if (type === 'leave') {
    const room = roomOf(pid);
    for (const c of cs) leaveCurrent(c);
    if (room) {
      const seat = room.seatOf(pid);
      if (seat && room.status !== 'playing') { room.seats = room.seats.filter(s => s !== seat); room.log(`${seat.name} 퇴장`); room.dirty = true; }
      room.tick(Date.now());
    }
  }
}

const server = http.createServer((req, res) => {
  const url = new URL(req.url, 'http://localhost');
  if (url.pathname === '/healthz') { res.writeHead(200); res.end('ok'); return; }
  if (url.pathname === '/events' && req.method === 'GET') {
    const pid = clean(url.searchParams.get('pid'), 40);
    if (pid.length < 12) { res.writeHead(400); res.end(); return; }
    res.writeHead(200, { 'content-type': 'text/event-stream; charset=utf-8', 'cache-control': 'no-cache, no-transform', connection: 'keep-alive', 'x-accel-buffering': 'no' });
    res.write('retry: 2000\n\n');
    const c = new Client(pid, res);
    if (!clients.has(pid)) clients.set(pid, new Set());
    clients.get(pid).add(c);
    c.emit('hello', { t: Date.now() });
    const ka = setInterval(() => { try { res.write(': ka\n\n'); } catch (e) {} }, 20000);
    req.on('close', () => {
      clearInterval(ka); c.alive = false;
      const set = clients.get(pid); if (set) { set.delete(c); if (!set.size) clients.delete(pid); }
      const room = rooms.get(c.code); leaveCurrent(c); if (room) room.tick(Date.now());
    });
    return;
  }
  if (url.pathname === '/api' && req.method === 'POST') {
    let body = '';
    req.on('data', d => { body += d; if (body.length > 10000) req.destroy(); });
    req.on('end', () => {
      let msg; try { msg = JSON.parse(body); } catch (e) { res.writeHead(400); res.end(); return; }
      res.writeHead(204); res.end();
      try { handle(msg); } catch (e) { console.error('handle error', e); }
    });
    return;
  }
  res.writeHead(200, { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'no-cache' });
  res.end(PAGE);
});

setInterval(() => {
  const now = Date.now();
  for (const [code, room] of rooms) {
    if (!room.socks.size && now - room.emptySince > 2 * 3600e3) { rooms.delete(code); continue; }
    try { room.tick(now); } catch (e) { console.error('tick error', code, e); }
  }
}, 400);

server.listen(PORT, () => console.log(`우리끼리 홀덤 서버 실행 중: http://localhost:${PORT}`));
