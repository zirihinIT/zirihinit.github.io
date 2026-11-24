// ================= セーブデータ（IndexedDB） =================
// 自己ベスト・選んだ消しゴム・きせかえ・名前・音量などを IndexedDB に保存する。
// 起動時に全部読み込んでから game.js を始めるので、ゲーム側は SAVE.getItem / SAVE.setItem をそのまま使える。
// ※ データベース名は一度決めたら絶対に変えない（変えると、それまでのセーブデータが読めなくなる）
(function(){
  const DB_NAME='plicy_gekiochi_ghvl41yr',STORE='kv',GAME_JS='game.js?v=20261124';
  const cache=new Map();let db=null;
  const SAVE=window.SAVE={
    getItem(k){return cache.has(k)?cache.get(k):null},
    setItem(k,v){v=String(v);cache.set(k,v);put(k,v)},
    removeItem(k){cache.delete(k);if(db)try{db.transaction(STORE,'readwrite').objectStore(STORE).delete(k)}catch(e){}}
  };
  function put(k,v){if(db)try{db.transaction(STORE,'readwrite').objectStore(STORE).put(v,k)}catch(e){}}
  function start(){const s=document.createElement('script');s.src=GAME_JS;document.body.appendChild(s)}
  // 以前の版（localStorage に保存していた頃）のデータを、初回だけ引き継ぐ
  function migrateOld(){let n=0;try{const ls=window.localStorage;
    for(let i=0;i<ls.length;i++){const k=ls.key(i);if(k&&k.indexOf('gekiochi')===0&&!cache.has(k)){const v=ls.getItem(k);cache.set(k,v);put(k,v);n++}}}catch(e){}return n}
  let done=false;const go=()=>{if(done)return;done=true;start()};
  // IndexedDB が使えない・遅いときも、セーブなしで遊べるようにする
  setTimeout(go,2500);
  try{
    const rq=indexedDB.open(DB_NAME,1);
    rq.onupgradeneeded=()=>{const d=rq.result;if(!d.objectStoreNames.contains(STORE))d.createObjectStore(STORE)};
    rq.onerror=go;rq.onblocked=go;
    rq.onsuccess=()=>{db=rq.result;
      try{const st=db.transaction(STORE,'readonly').objectStore(STORE),cur=st.openCursor();
        cur.onsuccess=()=>{const c=cur.result;if(c){if(!done)cache.set(String(c.key),c.value);c.continue()}else{if(!done&&!cache.size)migrateOld();go()}};
        cur.onerror=go}catch(e){go()}};
  }catch(e){go()}
})();
