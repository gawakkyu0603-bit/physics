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
  document.querySelectorAll('.return-explorer').forEach(panel => {
    const slider = panel.querySelector('input');
    const result = panel.querySelector('output');
    const weight = panel.querySelector('[data-weight]');
    const other = panel.querySelector('[data-other]');
    const dot = panel.querySelector('[data-curve-dot]');
    const refresh = () => {
      const w = Number(slider.value);
      const f = w*w + (1-w)*(1-w);
      result.value = f.toFixed(4);
      result.textContent = f.toFixed(4);
      weight.textContent = w.toFixed(2);
      other.textContent = (1-w).toFixed(2);
      if (dot) {dot.setAttribute('cx', (60+560*w).toFixed(1));dot.setAttribute('cy', (230-180*f).toFixed(1));}
    };
    slider.addEventListener('input', refresh);
    refresh();
  });
})();
