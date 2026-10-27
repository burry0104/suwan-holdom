# 우리끼리 홀덤

친구들과 방 코드(또는 초대 링크)로 모여서 하는 실시간 노리밋 텍사스 홀덤 웹사이트예요.

- 파일: `server.js`(서버), `index.html`(화면), `package.json`(실행 설정)
- 외부 패키지가 없어서 설치할 게 없어요. Node.js 18 이상이면 `npm start`로 실행돼요.

## Render에 올리기

1. GitHub에 새 저장소를 만들고 이 파일 3개를 올려요.
2. render.com에서 **New → Web Service**를 누르고 그 저장소를 골라요.
3. 설정값
   - Build Command: `npm install`
   - Start Command: `npm start`
   - Instance Type: **Free**
4. 배포가 끝나면 나오는 `https://….onrender.com` 주소가 게임 사이트예요.

무료 플랜은 15분 동안 아무도 접속하지 않으면 잠들고, 다음 접속 때 깨어나는 데 1분 정도 걸려요. 서버가 잠들거나 다시 배포되면 진행 중이던 방은 사라져요.
