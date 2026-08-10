/* Copyright 2026 The Capacity Atlas Authors */
/* SPDX-License-Identifier: Apache-2.0 */

(() => {
  const toggle = document.querySelector("[data-nav-toggle]");
  const nav = document.querySelector("[data-site-nav]");
  if (toggle && nav) {
    toggle.addEventListener("click", () => {
      const open = toggle.getAttribute("aria-expanded") !== "true";
      toggle.setAttribute("aria-expanded", String(open));
      nav.dataset.open = String(open);
    });
  }

  const form = document.querySelector("[data-problem-filters]");
  if (!form) return;
  const rows = [...document.querySelectorAll("[data-problem-row]")];
  const count = document.querySelector("[data-result-count]");
  const empty = document.querySelector("[data-empty-state]");
  const controls = [...form.elements].filter((element) => element.name);
  const params = new URLSearchParams(window.location.search);

  for (const control of controls) {
    if (params.has(control.name)) control.value = params.get(control.name) || "";
  }

  const matches = (row, values) => {
    const query = values.q.trim().toLowerCase();
    if (query && !row.dataset.search.includes(query)) return false;
    for (const [axis, value] of Object.entries(values)) {
      if (!value || axis === "q") continue;
      const selected = (row.dataset[axis] || "").split(" ");
      if (!selected.includes(value)) return false;
    }
    return true;
  };

  const apply = () => {
    const values = Object.fromEntries(new FormData(form));
    let visible = 0;
    for (const row of rows) {
      row.hidden = !matches(row, values);
      if (!row.hidden) visible += 1;
    }
    count.textContent = String(visible);
    empty.hidden = visible !== 0;

    const next = new URLSearchParams();
    for (const [key, value] of Object.entries(values)) if (value) next.set(key, value);
    const suffix = next.toString();
    history.replaceState(null, "", suffix ? `?${suffix}` : window.location.pathname);
  };

  form.addEventListener("input", apply);
  form.addEventListener("change", apply);
  form.addEventListener("reset", () => requestAnimationFrame(apply));
  apply();
})();
