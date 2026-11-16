// 旧アドレスの後片付け：古いキャッシュを消して自分を解除する
self.addEventListener("install",()=>self.skipWaiting());
self.addEventListener("activate",e=>{e.waitUntil((async()=>{
  await caches.delete("hokkori-v1");
  await self.registration.unregister();
  const cs=await self.clients.matchAll({type:"window"});cs.forEach(c=>c.navigate(c.url));
})());});
