/* =========================================================
   宇宙戦士デルタ・ナプラ ゲーム本体

   主な役割
   1. カメラ起動と端末内MediaPipe認識
   2. PeerJSによるPC・スマホ間の一時的な映像／結果通信
   3. 3つの課題HTMLの読み替えと連続成功数の管理
   4. Web Audio APIによる効果音
   5. Image Segmenterによる宇宙背景合成とFace Landmarker表情認識

   映像・名前・認識結果を録画／保存する処理はありません。
   ========================================================= */

const $ = (selector) => document.querySelector(selector);
const params = new URLSearchParams(location.search);
const requestedMode = params.get('mode');
const requestedRoom = params.get('room');

const screens = [...document.querySelectorAll('.screen')];
const participantTemplate = $('#participantTemplate');
const participants = new Map();
const dataConnections = new Map();
const mediaCalls = new Map();

const missionFiles = [
  'mission-meteor.html',
  'mission-kaiju.html',
  'mission-rescue.html'
];

let appMode = requestedMode === 'join' && requestedRoom ? 'join' : 'menu';
let peer = null;
let hostConnection = null;
let localStream = null;
let localParticipantId = 'local';
let localPlayerName = '司令PC';
let joinUrl = '';
let roomId = '';
let audioContext = null;
let soundEnabled = true;
let handLandmarker = null;
let poseLandmarker = null;
let imageSegmenter = null;
let faceLandmarker = null;
let processedStream = null;
let compositeReadyPromise = null;
let recognitionRunning = false;
let detectionFrame = 0;
let currentMissionIndex = 0;
let successStreak = 0;
let timerInterval = null;
let missionStartedAt = 0;
let missionIsRunning = false;
let toastTimer = null;

// 端末性能に応じて解像度と認識頻度を抑えます。
// スマホでは人物分離を約5回/秒、PCでは約8回/秒にしています。
const constrainedDevice = matchMedia('(max-width: 760px)').matches
  || (navigator.deviceMemory && navigator.deviceMemory <= 4)
  || (navigator.hardwareConcurrency && navigator.hardwareConcurrency <= 4);
const performanceProfile = constrainedDevice
  ? { cameraWidth: 640, canvasWidth: 360, outputFps: 15, handPoseInterval: 150, faceInterval: 220, segmentInterval: 200 }
  : { cameraWidth: 960, canvasWidth: 640, outputFps: 20, handPoseInterval: 95, faceInterval: 135, segmentInterval: 125 };

const backgroundImage = new Image();
backgroundImage.decoding = 'async';
backgroundImage.src = 'assets/space-background.jpg';
const personMaskCanvas = document.createElement('canvas');
const personMaskContext = personMaskCanvas.getContext('2d', { willReadFrequently: true });
const compositeWorkCanvas = document.createElement('canvas');
const compositeWorkContext = compositeWorkCanvas.getContext('2d');
let personMaskReady = false;
let segmentationPending = false;

// 認識結果が1フレームだけ揺れても発動しないための状態です。
const recognitionState = {
  candidate: null,
  stableFrames: 0,
  lastTriggeredAt: 0,
  lastVideoTime: -1,
  lastHandPoseAt: 0,
  lastFaceAt: 0,
  lastSegmentAt: 0
};

const expressionState = { smile: false, mouth: false, brow: false };

// ---------- 画面と案内 ----------
function showScreen(target) {
  screens.forEach((screen) => {
    const active = screen === target;
    screen.hidden = !active;
    screen.classList.toggle('is-active', active);
  });
}

function setConnectionStatus(text, state = '') {
  const element = $('#connectionStatus');
  element.querySelector('span').textContent = text;
  element.className = `header-status ${state ? `is-${state}` : ''}`;
}

function showToast(message, type = 'info', duration = 4200) {
  clearTimeout(toastTimer);
  const toast = $('#toast');
  toast.textContent = message;
  toast.className = `toast ${type === 'error' ? 'is-error' : ''}`;
  toast.hidden = false;
  toastTimer = setTimeout(() => { toast.hidden = true; }, duration);
}

function cameraErrorMessage(error) {
  if (!window.isSecureContext) {
    return 'カメラはHTTPSのページ、またはlocalhostで開いてください。GitHub Pagesに公開するとHTTPSで利用できます。';
  }
  switch (error?.name) {
    case 'NotAllowedError':
    case 'SecurityError':
      return 'カメラが許可されていません。アドレス欄の左にあるカメラ印から、このサイトのカメラを「許可」にしてください。';
    case 'NotReadableError':
    case 'AbortError':
      return 'カメラを開始できません。Zoom・Teamsなど、カメラを使っているアプリを閉じてから再読み込みしてください。';
    case 'NotFoundError':
      return '使用できるカメラが見つかりません。カメラの接続とWindowsの設定を確認してください。';
    case 'OverconstrainedError':
      return '指定したカメラ設定を利用できません。別のカメラで試してください。';
    default:
      return `カメラを開始できませんでした（${error?.name || '原因不明'}）。画面ボタンではゲームを試せます。`;
  }
}

function connectionErrorMessage(error) {
  const type = error?.type || '';
  if (!navigator.onLine) return 'インターネットにつながっていません。接続を確認してください。';
  if (type === 'peer-unavailable') return '大元のPCのルームが見つかりません。PC側のページを開いたまま、QRコードを読み直してください。';
  if (type === 'network' || type === 'server-error' || type === 'socket-error') return '通信サービスへ接続できません。しばらく待ってから再読み込みしてください。';
  if (type === 'browser-incompatible') return 'このブラウザは通信機能に対応していません。最新版のChromeまたはEdgeで開いてください。';
  return `通信に失敗しました${type ? `（${type}）` : ''}。ページを再読み込みして、もう一度お試しください。`;
}

// ---------- 音声 ----------
async function enableAudio() {
  try {
    if (!audioContext) audioContext = new (window.AudioContext || window.webkitAudioContext)();
    if (audioContext.state === 'suspended') await audioContext.resume();
    $('#audioUnlockButton').hidden = audioContext.state === 'running';
    if (audioContext.state === 'running') playConfirmSound();
  } catch (error) {
    $('#audioUnlockButton').hidden = false;
  }
}

function withAudio(callback) {
  if (!soundEnabled) return;
  if (!audioContext || audioContext.state !== 'running') {
    $('#audioUnlockButton').hidden = false;
    return;
  }
  callback(audioContext);
}

function playConfirmSound() {
  withAudio((ctx) => {
    const osc = ctx.createOscillator();
    const gain = ctx.createGain();
    osc.frequency.setValueAtTime(660, ctx.currentTime);
    gain.gain.setValueAtTime(.0001, ctx.currentTime);
    gain.gain.exponentialRampToValueAtTime(.08, ctx.currentTime + .015);
    gain.gain.exponentialRampToValueAtTime(.0001, ctx.currentTime + .18);
    osc.connect(gain).connect(ctx.destination); osc.start(); osc.stop(ctx.currentTime + .2);
  });
}

// △デルタ＝太鼓：短い低音とノイズで作っています。
function playDrum() {
  withAudio((ctx) => {
    const osc = ctx.createOscillator(); const gain = ctx.createGain();
    osc.type = 'sine'; osc.frequency.setValueAtTime(145, ctx.currentTime); osc.frequency.exponentialRampToValueAtTime(48, ctx.currentTime + .28);
    gain.gain.setValueAtTime(.25, ctx.currentTime); gain.gain.exponentialRampToValueAtTime(.0001, ctx.currentTime + .32);
    osc.connect(gain).connect(ctx.destination); osc.start(); osc.stop(ctx.currentTime + .34);
  });
}

// ▽ナプラ＝ラッパ：倍音の多い波を上向きに変化させています。
function playTrumpet() {
  withAudio((ctx) => {
    [0, .055, .11].forEach((delay, index) => {
      const osc = ctx.createOscillator(); const gain = ctx.createGain();
      osc.type = 'sawtooth'; osc.frequency.setValueAtTime([330, 392, 494][index], ctx.currentTime + delay);
      gain.gain.setValueAtTime(.0001, ctx.currentTime + delay); gain.gain.exponentialRampToValueAtTime(.055, ctx.currentTime + delay + .02); gain.gain.exponentialRampToValueAtTime(.0001, ctx.currentTime + delay + .28);
      osc.connect(gain).connect(ctx.destination); osc.start(ctx.currentTime + delay); osc.stop(ctx.currentTime + delay + .3);
    });
  });
}

// 協力成立・成功＝鈴
function playBell(success = true) {
  withAudio((ctx) => {
    const notes = success ? [660, 880, 1320] : [240, 190];
    notes.forEach((frequency, index) => {
      const osc = ctx.createOscillator(); const gain = ctx.createGain(); const start = ctx.currentTime + index * .11;
      osc.type = 'sine'; osc.frequency.value = frequency;
      gain.gain.setValueAtTime(.0001, start); gain.gain.exponentialRampToValueAtTime(.08, start + .01); gain.gain.exponentialRampToValueAtTime(.0001, start + .48);
      osc.connect(gain).connect(ctx.destination); osc.start(start); osc.stop(start + .5);
    });
  });
}

function playGestureSound(gesture) {
  if (gesture === 'delta') playDrum();
  else playTrumpet();
}

// Face Landmarkerの表情と音の組み合わせです。
function playExpressionSound(expression) {
  if (expression === 'smile') playDrum();
  else if (expression === 'mouth') playTrumpet();
  else if (expression === 'brow') playBell(true);
}

function toggleSound() {
  soundEnabled = !soundEnabled;
  $('#soundButton').textContent = soundEnabled ? '🔊' : '🔇';
  $('#soundButton').setAttribute('aria-label', soundEnabled ? '音をオフにする' : '音をオンにする');
  if (soundEnabled) enableAudio();
}

// ---------- カメラと参加者カード ----------
async function requestCamera() {
  if (localStream) return localStream;
  try {
    localStream = await navigator.mediaDevices.getUserMedia({
      video: {
        facingMode: 'user',
        width: { ideal: performanceProfile.cameraWidth },
        height: { ideal: Math.round(performanceProfile.cameraWidth * .75) },
        frameRate: { ideal: constrainedDevice ? 20 : 24, max: 30 }
      },
      audio: false
    });
    return localStream;
  } catch (error) {
    showToast(cameraErrorMessage(error), 'error', 8500);
    updateRecognitionStatus('カメラなし：画面ボタンで操作できます', 'error');
    return null;
  }
}

function createParticipant(id, name, stream, device = 'SMARTPHONE') {
  let participant = participants.get(id);
  if (!participant) {
    const card = participantTemplate.content.firstElementChild.cloneNode(true);
    card.dataset.participantId = id;
    participant = { id, name: name || '応援戦士', stream: null, card, lastGestureAt: 0 };
    participants.set(id, participant);
  }
  participant.card.classList.toggle('is-local-source', id === localParticipantId);
  participant.name = name || participant.name;
  participant.card.querySelector('.participant-name').textContent = participant.name;
  participant.card.querySelector('.participant-device').textContent = device;
  if (stream) {
    participant.stream = stream;
    const video = participant.card.querySelector('video');
    if (video.srcObject !== stream) video.srcObject = stream;
  }
  placeParticipantCards();
  updateParticipantCount();
  return participant;
}

async function prepareCompositeOutput() {
  if (compositeReadyPromise) return compositeReadyPromise;
  compositeReadyPromise = (async () => {
    const participant = participants.get(localParticipantId);
    const video = participant?.card.querySelector('video');
    const canvas = participant?.card.querySelector('.composite-canvas');
    if (!video || !canvas || !localStream) return null;

    if (video.readyState < 1) {
      await Promise.race([
        new Promise((resolve) => video.addEventListener('loadedmetadata', resolve, { once: true })),
        new Promise((resolve) => setTimeout(resolve, 1800))
      ]);
    }
    await video.play().catch(() => {});
    const sourceWidth = video.videoWidth || performanceProfile.cameraWidth;
    const sourceHeight = video.videoHeight || Math.round(sourceWidth * .75);
    canvas.width = Math.min(performanceProfile.canvasWidth, sourceWidth);
    canvas.height = Math.max(180, Math.round(canvas.width * sourceHeight / sourceWidth));
    compositeWorkCanvas.width = canvas.width;
    compositeWorkCanvas.height = canvas.height;
    drawCompositeFrame(video);

    if (typeof canvas.captureStream === 'function') {
      processedStream = canvas.captureStream(performanceProfile.outputFps);
    }
    return processedStream;
  })();
  return compositeReadyPromise;
}

function drawCover(context, source, width, height) {
  const sourceWidth = source.videoWidth || source.naturalWidth || source.width || width;
  const sourceHeight = source.videoHeight || source.naturalHeight || source.height || height;
  const scale = Math.max(width / sourceWidth, height / sourceHeight);
  const drawWidth = sourceWidth * scale, drawHeight = sourceHeight * scale;
  context.drawImage(source, (width - drawWidth) / 2, (height - drawHeight) / 2, drawWidth, drawHeight);
}

function drawCompositeFrame(video) {
  const participant = participants.get(localParticipantId);
  const canvas = participant?.card.querySelector('.composite-canvas');
  if (!canvas || !video || video.readyState < 2) return;
  const context = canvas.getContext('2d');
  const width = canvas.width, height = canvas.height;
  if (!width || !height) return;

  // 先に指定された宇宙画像を全面へ描きます。
  context.clearRect(0, 0, width, height);
  if (backgroundImage.complete && backgroundImage.naturalWidth) drawCover(context, backgroundImage, width, height);
  else { context.fillStyle = '#030919'; context.fillRect(0, 0, width, height); }

  if (!personMaskReady) return;
  compositeWorkContext.clearRect(0, 0, width, height);
  compositeWorkContext.save();
  compositeWorkContext.translate(width, 0);
  compositeWorkContext.scale(-1, 1);
  compositeWorkContext.drawImage(video, 0, 0, width, height);
  compositeWorkContext.globalCompositeOperation = 'destination-in';
  // 小さい信頼度マスクを拡大する際に補間と軽いぼかしを使い、輪郭を滑らかにします。
  compositeWorkContext.imageSmoothingEnabled = true;
  compositeWorkContext.imageSmoothingQuality = 'high';
  compositeWorkContext.filter = constrainedDevice ? 'blur(1.2px)' : 'blur(1.8px)';
  compositeWorkContext.drawImage(personMaskCanvas, 0, 0, width, height);
  compositeWorkContext.restore();
  compositeWorkContext.globalCompositeOperation = 'source-over';
  compositeWorkContext.filter = 'none';
  context.drawImage(compositeWorkCanvas, 0, 0);
}

function removeParticipant(id) {
  const participant = participants.get(id);
  if (!participant || id === localParticipantId) return;
  participant.card.remove();
  participants.delete(id);
  dataConnections.delete(id);
  const call = mediaCalls.get(id); if (call) call.close(); mediaCalls.delete(id);
  updateParticipantCount();
  showToast(`${participant.name}がルームから退出しました。`);
}

function placeParticipantCards() {
  let destination = null;
  if (!$('#hostLobbyScreen').hidden) destination = $('#lobbyParticipants');
  else if (!$('#missionScreen').hidden) destination = $('#missionParticipants');
  else if (!$('#joinPlayScreen').hidden) destination = $('#mobileCameraStage');
  if (!destination) return;
  participants.forEach((participant) => {
    // スマホ側には自分の映像だけ、大元PCには全員の映像を表示します。
    if (appMode !== 'join' || participant.id === localParticipantId) destination.append(participant.card);
  });
}

function updateParticipantCount() {
  $('#participantCount').textContent = participants.size;
  if (appMode === 'host') {
    const ready = Boolean(peer?.open);
    $('#startMissionButton').disabled = !ready;
    $('#lobbyHint').textContent = participants.size >= 2
      ? '仲間が到着しました。全員の準備ができたら出動！'
      : '最初の協力課題には、スマホからもう1人の参加が必要です。';
  }
}

function animateGesture(participantId, gesture) {
  const participant = participants.get(participantId);
  if (!participant) return;
  const card = participant.card;
  card.classList.remove('is-casting', 'is-napla');
  card.querySelector('.magic-overlay span').textContent = gesture === 'delta' ? '△' : '▽';
  card.querySelector('.participant-signal').textContent = gesture === 'delta' ? 'DELTA' : 'NAPLA';
  if (gesture === 'napla') card.classList.add('is-napla');
  void card.offsetWidth;
  card.classList.add('is-casting');
  clearTimeout(participant.gestureTimer);
  participant.gestureTimer = setTimeout(() => {
    card.classList.remove('is-casting', 'is-napla');
    card.querySelector('.participant-signal').textContent = '待機';
  }, 900);
}

function expressionLabel(expression) {
  return { smile: '笑顔 😀', mouth: '口を開いた 📣', brow: '眉アップ ✨' }[expression] || '表情';
}

function animateExpression(participantId, expression, held = false) {
  const participant = participants.get(participantId);
  if (!participant) return;
  const badge = participant.card.querySelector(`[data-expression="${expression}"]`);
  badge?.classList.add('is-active');
  participant.card.querySelector('.participant-signal').textContent = expressionLabel(expression);
  if (!held) {
    clearTimeout(participant.expressionTimer);
    participant.expressionTimer = setTimeout(() => {
      badge?.classList.remove('is-active');
      participant.card.querySelector('.participant-signal').textContent = '待機';
    }, 950);
  }
}

// ---------- PeerJS通信 ----------
function makeRoomId() {
  const bytes = crypto.getRandomValues(new Uint8Array(4));
  return `delta-${[...bytes].map((n) => n.toString(16).padStart(2, '0')).join('')}`;
}

function createPeer(id) {
  if (!window.Peer) throw new Error('PeerJSのデータを読み込めませんでした。インターネット接続を確認してください。');
  // 設定を省略すると無料のPeerJS Cloudシグナリングを利用します。
  return id ? new window.Peer(id, { debug: 1 }) : new window.Peer({ debug: 1 });
}

async function startHostMode() {
  appMode = 'host';
  localParticipantId = 'local-host';
  localPlayerName = '司令PC';
  showScreen($('#hostLobbyScreen'));
  setConnectionStatus('ルーム準備中');
  await enableAudio();
  const stream = await requestCamera();
  createParticipant(localParticipantId, localPlayerName, stream, 'MAIN PC');
  if (stream) await prepareCompositeOutput();
  try {
    roomId = makeRoomId();
    peer = createPeer(roomId);
    bindHostPeerEvents();
  } catch (error) {
    setConnectionStatus('通信エラー', 'error');
    showToast(error.message || connectionErrorMessage(error), 'error', 8000);
  }
  if (stream) initRecognition();
}

function bindHostPeerEvents() {
  peer.on('open', (id) => {
    roomId = id;
    const url = new URL('game.html', location.href);
    url.search = new URLSearchParams({ mode: 'join', room: roomId }).toString();
    joinUrl = url.href;
    $('#roomIdText').textContent = roomId;
    $('#joinUrlText').textContent = joinUrl;
    renderQr(joinUrl);
    setConnectionStatus('ルーム公開中', 'online');
    updateParticipantCount();
  });

  peer.on('connection', (connection) => setupIncomingDataConnection(connection));

  // スマホからの一方向カメラ映像を受け取ります。PCの映像は送り返しません。
  peer.on('call', (call) => {
    mediaCalls.set(call.peer, call);
    call.answer();
    call.on('stream', (stream) => {
      const existing = participants.get(call.peer);
      createParticipant(call.peer, call.metadata?.name || existing?.name || '応援戦士', stream);
    });
    call.on('close', () => removeParticipant(call.peer));
    call.on('error', () => showToast('参加者の映像接続が切れました。操作結果の通信は継続します。', 'error'));
  });

  peer.on('disconnected', () => {
    setConnectionStatus('再接続中', 'error');
    showToast('通信サービスとの接続が切れました。自動で再接続を試します。', 'error');
    if (!peer.destroyed) peer.reconnect();
  });
  peer.on('error', (error) => {
    // ルームIDが偶然重なったときだけ、新しいIDで再作成します。
    if (error.type === 'unavailable-id') {
      showToast('ルーム番号が重なったため、新しい番号を作っています。');
      peer.destroy(); roomId = makeRoomId(); peer = createPeer(roomId); bindHostPeerEvents(); return;
    }
    setConnectionStatus('通信エラー', 'error');
    showToast(connectionErrorMessage(error), 'error', 8000);
  });
}

function setupIncomingDataConnection(connection) {
  dataConnections.set(connection.peer, connection);
  connection.on('open', () => {
    const name = connection.metadata?.name || '応援戦士';
    createParticipant(connection.peer, name, null);
    connection.send({ type: 'welcome', roomId, name });
  });
  connection.on('data', (data) => handleHostData(connection.peer, data));
  connection.on('close', () => removeParticipant(connection.peer));
  connection.on('error', () => showToast('参加者との操作通信に失敗しました。', 'error'));
}

function handleHostData(peerId, data) {
  if (!data || typeof data !== 'object') return;
  if (data.type === 'hello') {
    const participant = createParticipant(peerId, String(data.name || '応援戦士').slice(0, 12), null);
    showHeroCutIn(participant.name);
  }
  if (data.type === 'gesture') {
    triggerGesture(data.gesture, {
      participantId: peerId,
      participantName: participants.get(peerId)?.name || '応援戦士',
      size: Number(data.size) || .45,
      source: data.source || 'remote'
    }, false);
  }
  if (data.type === 'expression' && ['smile', 'mouth', 'brow'].includes(data.expression)) {
    triggerExpression(data.expression, { participantId: peerId }, false);
  }
}

async function joinHostRoom() {
  const enteredName = $('#playerName').value.trim();
  if (!enteredName) {
    $('#playerName').focus(); showToast('参加するときの名前を入力してください。', 'error'); return;
  }
  localPlayerName = enteredName.slice(0, 12);
  await enableAudio();
  $('#joinRoomButton').disabled = true;
  $('#joinRoomButton').textContent = 'カメラを準備中...';
  const stream = await requestCamera();
  appMode = 'join';
  showScreen($('#joinPlayScreen'));
  localParticipantId = 'local-join';
  createParticipant(localParticipantId, localPlayerName, stream, 'THIS PHONE');
  if (stream) await prepareCompositeOutput();
  placeParticipantCards();
  $('#mobileCallsign').textContent = localPlayerName;
  setConnectionStatus('PCへ接続中');

  try {
    peer = createPeer();
    peer.on('open', () => {
      hostConnection = peer.connect(requestedRoom, { reliable: true, metadata: { name: localPlayerName } });
      hostConnection.on('open', () => {
        setConnectionStatus('PCと接続中', 'online');
        $('#mobileConnectionChip').textContent = '大元PCと接続中';
        $('#mobileConnectionChip').classList.add('is-online');
        hostConnection.send({ type: 'hello', name: localPlayerName });
        if (stream) {
          // Canvas captureStreamに対応する端末では、宇宙背景へ合成した映像をPCへ送ります。
          const outgoingStream = processedStream || stream;
          const call = peer.call(requestedRoom, outgoingStream, { metadata: { name: localPlayerName, composited: Boolean(processedStream) } });
          mediaCalls.set(requestedRoom, call);
          call.on('error', () => showToast('映像をPCへ送れませんでした。画面ボタンによる参加は継続できます。', 'error'));
        }
      });
      hostConnection.on('data', handleJoinData);
      hostConnection.on('close', showHostDisconnected);
      hostConnection.on('error', showHostDisconnected);
    });
    peer.on('disconnected', showHostDisconnected);
    peer.on('error', (error) => {
      setConnectionStatus('接続失敗', 'error');
      showToast(connectionErrorMessage(error), 'error', 9000);
    });
  } catch (error) {
    showToast(error.message || connectionErrorMessage(error), 'error', 9000);
  }
  if (stream) initRecognition();
}

function handleJoinData(data) {
  if (!data || typeof data !== 'object') return;
  if (data.type === 'mission') {
    $('#mobileInstruction').textContent = data.instruction || 'PC画面の指令を確認せよ';
    $('#mobileGestureReadout').textContent = data.title || 'ミッション進行中';
  }
  if (data.type === 'mission-result') {
    $('#mobileGestureReadout').textContent = data.success ? 'ミッション成功！' : 'もう一度力を合わせよう！';
    playBell(Boolean(data.success));
  }
  if (data.type === 'ending') {
    $('#mobileInstruction').textContent = '地球はこうして救われた！';
    $('#mobileGestureReadout').textContent = '3連続成功！';
    playBell(true);
  }
}

function showHostDisconnected() {
  setConnectionStatus('PCとの接続切断', 'error');
  $('#mobileConnectionChip').textContent = '接続が切れました';
  $('#mobileConnectionChip').classList.remove('is-online');
  showToast('大元のPCとの接続が切れました。PCが同じルームを開いているか確認し、QRコードを読み直してください。', 'error', 9000);
}

function renderQr(url) {
  const target = $('#qrCode'); target.replaceChildren();
  if (window.QRCode) {
    new window.QRCode(target, { text: url, width: 220, height: 220, colorDark: '#061329', colorLight: '#ffffff', correctLevel: window.QRCode.CorrectLevel.M });
  } else {
    target.innerHTML = '<p style="color:#07142f;text-align:center">QRコードを読み込めませんでした。下の「URLを文字で表示」を使用してください。</p>';
  }
}

function broadcast(data) {
  dataConnections.forEach((connection) => {
    if (connection.open) {
      try { connection.send(data); } catch (_) { /* 切断処理に任せます */ }
    }
  });
}

function showHeroCutIn(name) {
  const cutIn = $('#heroCutIn');
  $('#cutInName').textContent = name;
  cutIn.hidden = false;
  setTimeout(() => { cutIn.hidden = true; }, 2700);
}

// ---------- MediaPipe認識 ----------
function updateRecognitionStatus(text, state = '') {
  const element = $('#recognitionStatus');
  element.querySelector('span:last-child').textContent = text;
  element.className = `recognition-status ${state ? `is-${state}` : ''}`;
}

async function initRecognition() {
  if (recognitionRunning || !localStream) return;
  recognitionRunning = true;
  updateRecognitionStatus('人物分離・表情・手・姿勢AIを読み込み中...');
  try {
    const visionModule = await import('https://cdn.jsdelivr.net/npm/@mediapipe/tasks-vision@0.10.22-rc.20250304/vision_bundle.mjs');
    const { FilesetResolver, HandLandmarker, PoseLandmarker, ImageSegmenter, FaceLandmarker } = visionModule;
    const fileset = await FilesetResolver.forVisionTasks('https://cdn.jsdelivr.net/npm/@mediapipe/tasks-vision@0.10.22-rc.20250304/wasm');

    // 端末ごとにGPU→CPUの順で試し、一部のAIだけ失敗しても残りを動かします。
    async function createTask(TaskClass, options) {
      try {
        return await TaskClass.createFromOptions(fileset, {
          ...options,
          baseOptions: { ...options.baseOptions, delegate: 'GPU' }
        });
      } catch (_) {
        try { return await TaskClass.createFromOptions(fileset, options); }
        catch (error) { console.warn(`${TaskClass.name} loading error`, error); return null; }
      }
    }

    [handLandmarker, poseLandmarker, imageSegmenter, faceLandmarker] = await Promise.all([
      createTask(HandLandmarker, {
        baseOptions: { modelAssetPath: 'https://storage.googleapis.com/mediapipe-models/hand_landmarker/hand_landmarker/float16/1/hand_landmarker.task' },
        runningMode: 'VIDEO', numHands: 2,
        minHandDetectionConfidence: .55, minHandPresenceConfidence: .5, minTrackingConfidence: .5
      }),
      createTask(PoseLandmarker, {
        baseOptions: { modelAssetPath: 'https://storage.googleapis.com/mediapipe-models/pose_landmarker/pose_landmarker_lite/float16/1/pose_landmarker_lite.task' },
        runningMode: 'VIDEO', numPoses: 1,
        minPoseDetectionConfidence: .55, minPosePresenceConfidence: .5, minTrackingConfidence: .5
      }),
      createTask(ImageSegmenter, {
        baseOptions: { modelAssetPath: 'https://storage.googleapis.com/mediapipe-models/image_segmenter/selfie_segmenter_landscape/float16/latest/selfie_segmenter_landscape.tflite' },
        runningMode: 'VIDEO', outputConfidenceMasks: true, outputCategoryMask: false
      }),
      createTask(FaceLandmarker, {
        baseOptions: { modelAssetPath: 'https://storage.googleapis.com/mediapipe-models/face_landmarker/face_landmarker/float16/latest/face_landmarker.task' },
        runningMode: 'VIDEO', numFaces: 1, outputFaceBlendshapes: true,
        minFaceDetectionConfidence: .5, minFacePresenceConfidence: .5, minTrackingConfidence: .5
      })
    ]);

    if (![handLandmarker, poseLandmarker, imageSegmenter, faceLandmarker].some(Boolean)) throw new Error('すべての認識データを読み込めませんでした');
    const activeNames = [
      imageSegmenter && '人物分離', faceLandmarker && '表情', handLandmarker && '手', poseLandmarker && '姿勢'
    ].filter(Boolean).join('・');
    updateRecognitionStatus(`${activeNames}AI作動中`, 'ready');
    if (!imageSegmenter || !faceLandmarker) {
      showToast('一部の認識AIを読み込めませんでした。利用できる機能だけでゲームを続けます。', 'error', 7000);
    }
    runDetectionLoop();
  } catch (error) {
    recognitionRunning = false;
    updateRecognitionStatus('認識データを読み込めません：画面ボタンで操作できます', 'error');
    showToast('人物分離・表情・手・姿勢認識のデータを読み込めませんでした。インターネット接続を確認してください。画面ボタンとD・Nキーは利用できます。', 'error', 9000);
    console.warn('MediaPipe loading error', error);
  }
}

function distance(a, b) {
  return Math.hypot(a.x - b.x, a.y - b.y);
}

function detectHandTriangle(result) {
  const hands = result?.landmarks;
  if (!hands || hands.length < 2) return null;
  const left = hands[0], right = hands[1];
  const indexDistance = distance(left[8], right[8]);
  const thumbDistance = distance(left[4], right[4]);
  const indexY = (left[8].y + right[8].y) / 2;
  const thumbY = (left[4].y + right[4].y) / 2;
  const vertical = Math.abs(indexY - thumbY);
  // 指先同士が近く、上下に十分な高さがあるときだけ三角形とみなします。
  if (indexDistance > .17 || thumbDistance > .18 || vertical < .045) return null;
  const points = [left[4], left[8], right[4], right[8]];
  const xs = points.map((point) => point.x), ys = points.map((point) => point.y);
  const diagonal = Math.hypot(Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys));
  return { gesture: indexY < thumbY ? 'delta' : 'napla', size: Math.max(.12, Math.min(.95, diagonal * 2.35)), source: 'hands', landmarks: hands };
}

function detectArmTriangle(result) {
  const pose = result?.landmarks?.[0];
  if (!pose) return null;
  const leftShoulder = pose[11], rightShoulder = pose[12], leftElbow = pose[13], rightElbow = pose[14], leftWrist = pose[15], rightWrist = pose[16];
  const points = [leftShoulder, rightShoulder, leftElbow, rightElbow, leftWrist, rightWrist];
  if (points.some((point) => !point || (point.visibility ?? 1) < .45)) return null;
  const wristDistance = distance(leftWrist, rightWrist);
  const elbowDistance = distance(leftElbow, rightElbow);
  const wristY = (leftWrist.y + rightWrist.y) / 2;
  const elbowY = (leftElbow.y + rightElbow.y) / 2;
  const vertical = Math.abs(wristY - elbowY);
  if (wristDistance > .23 || elbowDistance < .20 || vertical < .07) return null;
  return { gesture: wristY < elbowY ? 'delta' : 'napla', size: Math.max(.18, Math.min(.95, (elbowDistance + vertical) * 1.25)), source: 'arms', landmarks: [pose] };
}

function stabilizeRecognition(candidate) {
  const now = performance.now();
  if (!candidate) {
    recognitionState.candidate = null; recognitionState.stableFrames = 0; return;
  }
  if (recognitionState.candidate === candidate.gesture) recognitionState.stableFrames += 1;
  else { recognitionState.candidate = candidate.gesture; recognitionState.stableFrames = 1; }
  if (recognitionState.stableFrames >= 4 && now - recognitionState.lastTriggeredAt > 900) {
    recognitionState.lastTriggeredAt = now;
    recognitionState.stableFrames = 0;
    triggerGesture(candidate.gesture, {
      participantId: localParticipantId,
      participantName: localPlayerName,
      size: candidate.size,
      source: candidate.source
    });
  }
}

function drawLandmarks(handResult, poseResult) {
  const participant = participants.get(localParticipantId); if (!participant) return;
  const canvas = participant.card.querySelector('.landmark-canvas');
  const video = participant.card.querySelector('video');
  const width = video.videoWidth || 640, height = video.videoHeight || 480;
  if (canvas.width !== width || canvas.height !== height) { canvas.width = width; canvas.height = height; }
  const ctx = canvas.getContext('2d'); ctx.clearRect(0, 0, width, height);
  ctx.lineWidth = Math.max(2, width / 260); ctx.strokeStyle = '#54ecff'; ctx.fillStyle = '#ffd84a';
  const handLines = [[4,8]];
  (handResult?.landmarks || []).forEach((hand) => {
    handLines.forEach(([a,b]) => {ctx.beginPath();ctx.moveTo(hand[a].x*width,hand[a].y*height);ctx.lineTo(hand[b].x*width,hand[b].y*height);ctx.stroke()});
    [4,8].forEach((i) => {ctx.beginPath();ctx.arc(hand[i].x*width,hand[i].y*height,5,0,Math.PI*2);ctx.fill()});
  });
  const pose = poseResult?.landmarks?.[0];
  if (pose) {
    [[11,13],[13,15],[12,14],[14,16],[15,16]].forEach(([a,b]) => {ctx.beginPath();ctx.moveTo(pose[a].x*width,pose[a].y*height);ctx.lineTo(pose[b].x*width,pose[b].y*height);ctx.stroke()});
  }
}

function updatePersonMask(result) {
  const masks = result?.confidenceMasks || [];
  const personMask = masks.length > 1 ? masks[1] : masks[0];
  if (!personMask || !personMaskContext) return;
  try {
    const values = personMask.getAsFloat32Array();
    const width = personMask.width, height = personMask.height;
    if (personMaskCanvas.width !== width || personMaskCanvas.height !== height) {
      personMaskCanvas.width = width; personMaskCanvas.height = height;
    }
    const imageData = personMaskContext.createImageData(width, height);
    for (let index = 0; index < values.length; index += 1) {
      // 0.28～0.72の間をなめらかにつなぎ、髪や肩のギザつきを減らします。
      const normalized = Math.max(0, Math.min(1, (values[index] - .28) / .44));
      const smooth = normalized * normalized * (3 - 2 * normalized);
      const pixel = index * 4;
      imageData.data[pixel] = 255;
      imageData.data[pixel + 1] = 255;
      imageData.data[pixel + 2] = 255;
      imageData.data[pixel + 3] = Math.round(smooth * 255);
    }
    personMaskContext.putImageData(imageData, 0, 0);
    personMaskReady = true;
  } finally {
    masks.forEach((mask) => mask?.close?.());
  }
}

function runSegmentation(video, timestamp) {
  if (!imageSegmenter || segmentationPending) return;
  segmentationPending = true;
  try {
    imageSegmenter.segmentForVideo(video, timestamp, (result) => {
      try { updatePersonMask(result); }
      finally { segmentationPending = false; }
    });
  } catch (error) {
    segmentationPending = false;
    console.warn('Image segmentation error', error);
  }
}

function blendshapeScore(categories, name) {
  return categories.find((category) => category.categoryName === name)?.score || 0;
}

function analyzeFaceExpressions(result) {
  const categories = result?.faceBlendshapes?.[0]?.categories;
  const participant = participants.get(localParticipantId);
  if (!participant) return;
  const active = categories ? {
    smile: (blendshapeScore(categories, 'mouthSmileLeft') + blendshapeScore(categories, 'mouthSmileRight')) / 2 > .52,
    mouth: blendshapeScore(categories, 'jawOpen') > .52,
    brow: Math.max(
      blendshapeScore(categories, 'browInnerUp'),
      (blendshapeScore(categories, 'browOuterUpLeft') + blendshapeScore(categories, 'browOuterUpRight')) / 2
    ) > .48
  } : { smile: false, mouth: false, brow: false };

  Object.entries(active).forEach(([expression, isActive]) => {
    participant.card.querySelector(`[data-expression="${expression}"]`)?.classList.toggle('is-active', isActive);
    // 表情を続けている間は一度だけ発動し、いったん戻すと再び発動できます。
    if (isActive && !expressionState[expression]) {
      triggerExpression(expression, { participantId: localParticipantId, held: true });
    }
    expressionState[expression] = isActive;
  });
  if (!Object.values(active).some(Boolean) && !participant.card.classList.contains('is-casting')) {
    participant.card.querySelector('.participant-signal').textContent = '待機';
  }
}

function runDetectionLoop() {
  cancelAnimationFrame(detectionFrame);
  const loop = () => {
    if (!recognitionRunning) return;
    const participant = participants.get(localParticipantId);
    const video = participant?.card.querySelector('video');
    const now = performance.now();
    if (video && video.readyState >= 2) {
      drawCompositeFrame(video);
      if (video.currentTime !== recognitionState.lastVideoTime) {
        recognitionState.lastVideoTime = video.currentTime;

        if ((handLandmarker || poseLandmarker) && now - recognitionState.lastHandPoseAt >= performanceProfile.handPoseInterval) {
          recognitionState.lastHandPoseAt = now;
          try {
            const hands = handLandmarker?.detectForVideo(video, now) || null;
            const pose = poseLandmarker?.detectForVideo(video, now) || null;
            const candidate = detectHandTriangle(hands) || detectArmTriangle(pose);
            stabilizeRecognition(candidate); drawLandmarks(hands, pose);
            if (appMode === 'join') $('#mobileGestureReadout').textContent = candidate ? `${candidate.gesture === 'delta' ? '△ デルタ' : '▽ ナプラ'}を確認中...` : '認識待ち';
          } catch (error) { console.warn('Hand/Pose detection error', error); }
        }

        if (faceLandmarker && now - recognitionState.lastFaceAt >= performanceProfile.faceInterval) {
          recognitionState.lastFaceAt = now;
          try { analyzeFaceExpressions(faceLandmarker.detectForVideo(video, now)); }
          catch (error) { console.warn('Face detection error', error); }
        }

        if (imageSegmenter && now - recognitionState.lastSegmentAt >= performanceProfile.segmentInterval) {
          recognitionState.lastSegmentAt = now;
          runSegmentation(video, now);
        }
      }
    }
    detectionFrame = requestAnimationFrame(loop);
  };
  detectionFrame = requestAnimationFrame(loop);
}

// ---------- ジェスチャー・ミッション ----------
function triggerGesture(gesture, detail = {}, sendToHost = true) {
  if (!['delta', 'napla'].includes(gesture)) return;
  const payload = {
    type: 'gesture', gesture,
    participantId: detail.participantId || localParticipantId,
    participantName: detail.participantName || localPlayerName,
    size: Math.max(.05, Math.min(.95, Number(detail.size) || .55)),
    source: detail.source || 'button', timestamp: Date.now()
  };

  animateGesture(payload.participantId, gesture);
  playGestureSound(gesture);

  if (appMode === 'join') {
    $('#mobileGestureReadout').textContent = gesture === 'delta' ? '△ デルタ発動！' : '▽ ナプラ発動！';
    if (sendToHost && hostConnection?.open) hostConnection.send(payload);
    else if (sendToHost) showToast('PCと接続していないため、操作結果を送れません。', 'error');
  }

  if (appMode === 'host' && missionIsRunning && $('#missionFrame').contentWindow) {
    $('#missionFrame').contentWindow.postMessage(payload, '*');
  }
}

function triggerExpression(expression, detail = {}, sendToHost = true) {
  if (!['smile', 'mouth', 'brow'].includes(expression)) return;
  const participantId = detail.participantId || localParticipantId;
  animateExpression(participantId, expression, Boolean(detail.held));
  playExpressionSound(expression);

  const payload = { type: 'expression', expression, timestamp: Date.now() };
  if (appMode === 'join' && sendToHost && hostConnection?.open) hostConnection.send(payload);
}

function startMissionSequence(reset = true) {
  appMode = 'host';
  if (reset) { currentMissionIndex = 0; successStreak = 0; }
  showScreen($('#missionScreen'));
  placeParticipantCards();
  updateStreakMeter();
  loadMission();
}

function loadMission() {
  clearInterval(timerInterval); missionIsRunning = false;
  $('#timerText').textContent = '10.0';
  $('#missionFrame').src = `${missionFiles[currentMissionIndex]}?run=${Date.now()}`;
  setConnectionStatus(`ミッション ${currentMissionIndex + 1}`, 'online');
}

function beginMission(title, instruction) {
  missionIsRunning = true;
  missionStartedAt = performance.now();
  $('#missionFrame').contentWindow.postMessage({ type: 'mission-start', participantCount: participants.size }, '*');
  broadcast({ type: 'mission', title, instruction, index: currentMissionIndex });
  clearInterval(timerInterval);
  timerInterval = setInterval(() => {
    const remaining = Math.max(0, 10 - (performance.now() - missionStartedAt) / 1000);
    $('#timerText').textContent = remaining.toFixed(1);
    if (remaining <= 0) clearInterval(timerInterval);
  }, 50);
}

function handleMissionResult(data) {
  if (!missionIsRunning) return;
  missionIsRunning = false; clearInterval(timerInterval); $('#timerText').textContent = '0.0';
  if (data.success) {
    successStreak += 1; playBell(true);
    showToast(`ミッション成功！　連続成功 ${successStreak}/3`);
  } else {
    successStreak = 0; playBell(false);
    showToast(data.reason === 'need-two' ? '失敗：この課題には二人以上の力が必要です。' : 'ミッション失敗。連続成功数は0に戻ります。', 'error');
  }
  updateStreakMeter();
  broadcast({ type: 'mission-result', success: Boolean(data.success), streak: successStreak });
  if (successStreak >= 3) setTimeout(showEnding, 1900);
  else {
    currentMissionIndex = (currentMissionIndex + 1) % missionFiles.length;
    setTimeout(loadMission, 2200);
  }
}

function updateStreakMeter() {
  [$('#streakOne'), $('#streakTwo'), $('#streakThree')].forEach((element, index) => element.classList.toggle('is-on', successStreak > index));
}

function showEnding() {
  showScreen($('#endingScreen'));
  setConnectionStatus('地球防衛成功', 'online');
  const team = $('#endingTeam'); team.replaceChildren();
  participants.forEach((participant) => {
    const badge = document.createElement('span'); badge.textContent = `⚡ ${participant.name}`; team.append(badge);
  });
  broadcast({ type: 'ending' });
  playBell(true); setTimeout(() => playBell(true), 650);
}

// iframeから受け取るメッセージは、現在の課題画面からのものだけ処理します。
addEventListener('message', (event) => {
  if (event.source !== $('#missionFrame').contentWindow) return;
  const data = event.data || {};
  if (data.type === 'mission-ready') beginMission(data.title, data.instruction);
  if (data.type === 'mission-result') handleMissionResult(data);
});

// ---------- ボタン・キーボード・回線状態 ----------
$('#hostModeButton').addEventListener('click', startHostMode);
$('#joinRoomButton').addEventListener('click', joinHostRoom);
$('#playerName').addEventListener('keydown', (event) => { if (event.key === 'Enter') joinHostRoom(); });
$('#startMissionButton').addEventListener('click', () => { enableAudio(); startMissionSequence(true); });
$('#testCameraButton').addEventListener('click', async () => {
  await enableAudio(); const stream = await requestCamera();
  if (stream) {
    createParticipant(localParticipantId, localPlayerName, stream, 'MAIN PC');
    await prepareCompositeOutput(); initRecognition();
    showToast('人物が宇宙背景へ合成されました。');
  }
});
$('#copyUrlButton').addEventListener('click', async () => {
  try { await navigator.clipboard.writeText(joinUrl); showToast('参加URLをコピーしました。'); }
  catch (_) { showToast('コピーできませんでした。「URLを文字で表示」から選択してください。', 'error'); }
});
$('#soundButton').addEventListener('click', toggleSound);
$('#audioUnlockButton').addEventListener('click', enableAudio);
$('#helpButton').addEventListener('click', () => $('#helpDialog').showModal());
$('#deltaButton').addEventListener('click', () => triggerGesture('delta', { size: .58 }));
$('#naplaButton').addEventListener('click', () => triggerGesture('napla', { size: .58 }));
$('#mobileDeltaButton').addEventListener('click', () => triggerGesture('delta', { size: .58 }));
$('#mobileNaplaButton').addEventListener('click', () => triggerGesture('napla', { size: .58 }));
$('#playAgainButton').addEventListener('click', () => startMissionSequence(true));

document.addEventListener('keydown', (event) => {
  if (event.repeat || ['INPUT', 'TEXTAREA'].includes(document.activeElement?.tagName)) return;
  const key = event.key.toLowerCase();
  if (key === 'd' || event.key === 'ArrowUp') triggerGesture('delta', { size: event.shiftKey ? .82 : .58, source: 'keyboard' });
  if (key === 'n' || event.key === 'ArrowDown') triggerGesture('napla', { size: event.shiftKey ? .82 : .58, source: 'keyboard' });
  if (key === 'm') toggleSound();
  if (key === 'h' || event.key === '?') $('#helpDialog').showModal();
});

addEventListener('offline', () => {
  setConnectionStatus('オフライン', 'error');
  showToast('インターネットにつながっていません。カメラの手動操作はできますが、スマホ通信と認識データの読み込みはできません。', 'error', 9000);
});
addEventListener('online', () => {
  showToast('インターネット接続が戻りました。');
  if (peer?.open) setConnectionStatus(appMode === 'host' ? 'ルーム公開中' : 'PCと接続中', 'online');
});

addEventListener('beforeunload', () => {
  cancelAnimationFrame(detectionFrame); clearInterval(timerInterval);
  localStream?.getTracks().forEach((track) => track.stop());
  processedStream?.getTracks().forEach((track) => track.stop());
  handLandmarker?.close?.(); poseLandmarker?.close?.();
  imageSegmenter?.close?.(); faceLandmarker?.close?.();
  peer?.destroy();
});

// QRコードの参加URLなら名前入力へ、それ以外は大元PCのメニューから開始します。
if (requestedMode === 'join' && requestedRoom) {
  showScreen($('#joinSetupScreen'));
  setConnectionStatus('参加準備');
  setTimeout(() => $('#playerName').focus(), 100);
} else {
  showScreen($('#menuScreen'));
}
