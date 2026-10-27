/* Curated links between the written theorem and verbatim, pinned Lean excerpts.
   Works both as a page and when opened in the site's proof-sheet stack. */
(function () {
  "use strict";
  function init(root) {
    var data = root.querySelector("#alignment-data");
    if (!data || data.dataset.ready) return;
    data.dataset.ready = "true";
    var matches = JSON.parse(data.textContent);
    var select = root.querySelector("#lean-part");
    var targets = Array.from(root.querySelectorAll("[data-align]"));
    var panels = Array.from(root.querySelectorAll("[data-source-panel]"));
    var label = root.querySelector(".alignment-label");
    var description = root.querySelector(".alignment-description");
    var pinned = null, pinnedPanel = "ii";

    function showPanel(key) {
      select.value = key;
      panels.forEach(function (p) { p.hidden = p.dataset.sourcePanel !== key; });
    }
    function paint(key, keepPanel) {
      targets.forEach(function (t) {
        var on = t.dataset.align === key;
        t.classList.toggle("is-matched", on);
        t.classList.toggle("is-pinned", on && key === pinned);
        t.setAttribute("aria-pressed", on && key === pinned ? "true" : "false");
      });
      root.querySelectorAll("[data-pick]").forEach(function (t) {
        t.classList.toggle("is-active", t.dataset.pick === key);
      });
      if (key) {
        var entry = matches[key];
        if (!keepPanel) showPanel(entry[0]);
        label.textContent = entry[1];
        description.textContent = entry[2];
      } else {
        label.textContent = "Follow the correspondence";
        description.textContent = "Hover to preview. Click or press Enter to keep a match highlighted and bring both sides into view.";
      }
    }
    function reveal(target) {
      if (!target) return;
      var scroller = target.closest(".comparison-scroll");
      if (!scroller) return;
      var r = target.getBoundingClientRect(), s = scroller.getBoundingClientRect();
      if (r.top < s.top + 12 || r.bottom > s.bottom - 12) {
        scroller.scrollTop += r.top - s.top - scroller.clientHeight / 4;
      }
    }
    function choose(key, origin) {
      pinned = key;
      // Keep the current source part when selecting a shared hypothesis in Lean.
      var fromLean = origin && origin.closest(".source-panel");
      paint(key, !!fromLean);
      pinnedPanel = select.value;
      revealMatch(key);
      if (!root.closest(".sheet")) {
        var url = new URL(location.href);
        url.hash = key ? "match=" + key : "";
        history.replaceState(history.state, "", url);
      }
    }
    function revealMatch(key) {
      [".written-scroll", '.source-panel:not([hidden])'].forEach(function (selector) {
        var side = root.querySelector(selector);
        reveal(side && side.querySelector('[data-align="' + key + '"]'));
      });
    }
    // Inline math may gain its own line after typesetting or a viewport resize.
    // Keep the pinned match visible after that layout change as well.
    window.addEventListener("proof-layout", function () {
      if (pinned && root.isConnected) requestAnimationFrame(function () { revealMatch(pinned); });
    });
    function restore() { showPanel(pinnedPanel); paint(pinned, true); }
    root.addEventListener("pointerover", function (ev) {
      var t = ev.target.closest("[data-align]");
      if (t && root.contains(t) && !t.contains(ev.relatedTarget)) paint(t.dataset.align, !!t.closest(".source-panel"));
    });
    root.addEventListener("pointerout", function (ev) {
      var t = ev.target.closest("[data-align]");
      if (t && !t.contains(ev.relatedTarget)) restore();
    });
    root.addEventListener("focusin", function (ev) {
      var t = ev.target.closest("[data-align]");
      if (t) paint(t.dataset.align, !!t.closest(".source-panel"));
    });
    root.addEventListener("focusout", function (ev) {
      if (ev.target.closest("[data-align]")) restore();
    });
    root.addEventListener("click", function (ev) {
      if (ev.target.closest("a")) return;
      var pick = ev.target.closest("[data-pick]");
      var t = ev.target.closest("[data-align]");
      if (pick) choose(pick.dataset.pick);
      else if (t) choose(t.dataset.align, t);
      else if (ev.target.closest(".clear-match")) {
        pinned = null;
        paint(null, true);
        if (!root.closest(".sheet")) history.replaceState(history.state, "", location.pathname + location.search);
      }
    });
    root.addEventListener("keydown", function (ev) {
      if ((ev.key === "Enter" || ev.key === " ") && ev.target.matches("[data-align]")) {
        ev.preventDefault(); choose(ev.target.dataset.align, ev.target);
      }
      if (ev.key === "Escape") { pinned = null; paint(null, true); }
    });
    select.addEventListener("change", function () {
      pinned = null; pinnedPanel = select.value; showPanel(select.value); paint(null, true);
    });
    function followHash() {
      var initial = /^#match=([a-z0-9]+)$/.exec(location.hash);
      if (initial && matches[initial[1]]) choose(initial[1]);
    }
    if (!root.closest(".sheet")) window.addEventListener("hashchange", followHash);
    if (/^#match=/.test(location.hash)) {
      var applyInitial = followHash;
      if (window.MathJax && MathJax.startup && MathJax.startup.promise) MathJax.startup.promise.then(applyInitial);
      else applyInitial();
    }
  }
  window.initTheoremComparison = init;
  init(document.querySelector("main.content") || document);
})();
