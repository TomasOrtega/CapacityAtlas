(() => {
  "use strict";

  const navToggle = document.querySelector("[data-nav-toggle]");
  const siteNav = document.querySelector("[data-site-nav]");

  if (navToggle && siteNav) {
    navToggle.addEventListener("click", () => {
      const open = siteNav.classList.toggle("is-open");
      navToggle.setAttribute("aria-expanded", String(open));
    });

    siteNav.addEventListener("click", (event) => {
      if (event.target instanceof HTMLAnchorElement) {
        siteNav.classList.remove("is-open");
        navToggle.setAttribute("aria-expanded", "false");
      }
    });
  }

  const panel = document.querySelector("[data-filter-panel]");
  if (!panel) return;

  const search = panel.querySelector("[data-problem-search]");
  const filters = Array.from(panel.querySelectorAll("[data-filter]"));
  const clear = panel.querySelector("[data-clear-filters]");
  const cards = Array.from(document.querySelectorAll("[data-problem-card]"));
  const resultCount = document.querySelector("[data-result-count]");
  const emptyState = document.querySelector("[data-empty-state]");

  const normalise = (value) => value.trim().toLowerCase();

  const applyFilters = () => {
    const query = search ? normalise(search.value) : "";
    const selected = Object.fromEntries(
      filters.map((filter) => [filter.dataset.filter, filter.value])
    );

    let visible = 0;
    cards.forEach((card) => {
      const searchMatches = !query || card.dataset.search.includes(query);
      const filterMatches = Object.entries(selected).every(([key, value]) => {
        return value === "all" || card.dataset[key] === value;
      });
      const show = searchMatches && filterMatches;
      card.hidden = !show;
      if (show) visible += 1;
    });

    if (resultCount) resultCount.textContent = String(visible);
    if (emptyState) emptyState.hidden = visible !== 0;
  };

  if (search) search.addEventListener("input", applyFilters);
  filters.forEach((filter) => filter.addEventListener("change", applyFilters));

  if (clear) {
    clear.addEventListener("click", () => {
      if (search) search.value = "";
      filters.forEach((filter) => {
        filter.value = "all";
      });
      applyFilters();
      if (search) search.focus();
    });
  }

  const query = new URLSearchParams(window.location.search).get("q");
  if (query && search) {
    search.value = query;
  }
  applyFilters();
})();
