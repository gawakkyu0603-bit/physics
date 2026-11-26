(() => {
  const bar = document.querySelector('.progress');
  const progress = () => {
    const range = document.documentElement.scrollHeight - innerHeight;
    if (bar) bar.style.width = `${range > 0 ? Math.min(100, 100 * scrollY / range) : 0}%`;
  };
  addEventListener('scroll', progress, {passive: true});
  addEventListener('resize', progress, {passive: true});
  progress();
  const toc = document.querySelector('.toc details');
  if (toc && matchMedia('(max-width: 1000px)').matches) toc.open = false;
})();
