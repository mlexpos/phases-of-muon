/* Phases of Muon proofs: stacked sheets, statement previews, graph interactions.
   A reference link (a.ref, a.open-proof, a.thm-name, constellation stars) opens its target
   page as a full-screen sheet over the current one. Closing a sheet (button, Esc, browser
   Back) returns to the page underneath at the same scroll position. The open stack is kept
   in the URL hash (#open=r.lem.app-dyn-block.html~r.thm.app-dyn-main.html) so it can be
   linked and restored. */
(function () {
  "use strict";
  var stack = [];            // [{el, url, title}]
  var baseScroll = 0;        // scroll position of the page under the first sheet
  var cache = {};            // url -> Promise<Document>
  var base = document.querySelector("main.content");

  function pageOf(href) {
    var a = document.createElement("a");
    a.href = href;
    var file = a.pathname.split("/").pop() || "index.html";
    return {file: file, hash: a.hash ? a.hash.slice(1) : "", sameSite: a.host === location.host};
  }

  function isLocal(href) {
    if (!href || href.charAt(0) === "#") return false;
    if (/^[a-z]+:/i.test(href) && href.indexOf(location.origin) !== 0) return false;
    return /\.html(#.*)?$/.test(href) && !/^index\.html/.test(pageOf(href).file);
  }

  function fetchDoc(file) {
    if (!cache[file]) {
      cache[file] = fetch(file).then(function (r) {
        if (!r.ok) throw new Error(r.status + " " + file);
        return r.text();
      }).then(function (t) { return new DOMParser().parseFromString(t, "text/html"); });
    }
    return cache[file];
  }

  function typeset(el) {
    if (window.MathJax && MathJax.typesetPromise) {
      return MathJax.startup.promise.then(function () { return MathJax.typesetPromise([el]); })
        .then(function () { fitWide(el); }).catch(function () {});
    }
    return Promise.resolve();
  }

  // MathJax cannot break inline formulas; one wider than its line gets a line of its own
  // that scrolls sideways, so the page itself never scrolls horizontally on a phone.
  function fitWide(root) {
    (root || document).querySelectorAll(".mi").forEach(function (m) {
      var host = m.closest(".p, li, .thm-body, figcaption") || m.parentElement;
      if (!host) return;
      m.classList.remove("mi-wide");
      if (m.getBoundingClientRect().width > host.getBoundingClientRect().width) m.classList.add("mi-wide");
    });
    window.dispatchEvent(new Event("proof-layout"));
  }
  if (window.MathJax || document.querySelector(".mi")) {
    var waitMJ = setInterval(function () {
      if (window.MathJax && MathJax.startup && MathJax.startup.promise) {
        clearInterval(waitMJ);
        MathJax.startup.promise.then(function () { fitWide(document); });
      }
    }, 100);
    window.addEventListener("resize", function () { fitWide(document); });
  }

  function crumbs() {
    var parts = [{title: document.title, depth: 0}];
    stack.forEach(function (s, i) { parts.push({title: s.title, depth: i + 1}); });
    return parts;
  }

  function renderBars() {
    var parts = crumbs();
    stack.forEach(function (s, i) {
      var c = s.el.querySelector(".crumbs");
      c.innerHTML = "";
      parts.slice(0, i + 2).forEach(function (p, k) {
        if (k) { var sep = document.createElement("span"); sep.className = "sep"; sep.textContent = "/"; c.appendChild(sep); }
        if (k === i + 1) {
          var cur = document.createElement("span"); cur.className = "cur"; cur.textContent = p.title; c.appendChild(cur);
        } else {
          var b = document.createElement("button"); b.type = "button"; b.textContent = shortTitle(p.title);
          b.addEventListener("click", function () { closeTo(p.depth); });
          c.appendChild(b);
        }
      });
      c.scrollLeft = c.scrollWidth;
    });
  }

  function shortTitle(t) { return t.length > 42 ? t.slice(0, 40) + "…" : t; }

  function writeHash(push) {
    var h = stack.length ? "#open=" + stack.map(function (s) { return s.url; }).join("~") : location.pathname.split("/").pop();
    var state = {depth: stack.length};
    if (push) history.pushState(state, "", stack.length ? h : location.pathname);
    else history.replaceState(state, "", stack.length ? h : location.pathname);
  }

  function openSheet(href, opts) {
    opts = opts || {};
    var p = pageOf(href);
    var url = p.file + (p.hash ? "#" + p.hash : "");
    // a link to the page already on top only scrolls
    var top = stack.length ? stack[stack.length - 1] : null;
    var topFile = top ? pageOf(top.url).file : location.pathname.split("/").pop();
    if (p.file === topFile && p.hash) { scrollToAnchor(top ? top.el : document, p.hash); return; }
    var el = document.createElement("div");
    el.className = "sheet";
    el.setAttribute("role", "dialog");
    el.setAttribute("aria-modal", "true");
    el.innerHTML = '<div class="sheet-bar"><button type="button" class="sheet-close" aria-label="Close">← Back</button>' +
      '<div class="crumbs"></div><a class="sheet-page" href="' + p.file + '">Open as page</a></div>' +
      '<main class="content"><div class="sheet-loading">Loading…</div></main>';
    if (!stack.length) baseScroll = window.scrollY;
    document.body.appendChild(el);
    document.documentElement.style.overflow = "hidden";
    var entry = {el: el, url: url, title: "…"};
    stack.push(entry);
    el.querySelector(".sheet-close").addEventListener("click", function () { closeTo(stack.indexOf(entry)); });
    renderBars();
    if (!opts.restoring) writeHash(true);
    return fetchDoc(p.file).then(function (doc) {
      var main = doc.querySelector("main.content");
      var box = el.querySelector("main.content");
      box.innerHTML = main ? main.innerHTML : "<p>Page not found.</p>";
      if (main && main.dataset.kind) el.classList.add("kind-" + main.dataset.kind);
      if (window.initTheoremComparison) window.initTheoremComparison(box);
      entry.title = (main && main.getAttribute("data-title")) || doc.title;
      renderBars();
      el.querySelector(".sheet-close").focus({preventScroll: true});
      return typeset(box).then(function () { if (p.hash) scrollToAnchor(el, p.hash); });
    }).catch(function (e) {
      el.querySelector("main.content").innerHTML = '<p class="sheet-loading">Could not load this page (' + e.message + '). <a href="' + p.file + '">Open it directly.</a></p>';
    });
  }

  function scrollToAnchor(root, id) {
    var t = (root.querySelector ? root : document).querySelector('[id="' + id.replace(/"/g, "") + '"]');
    if (!t) return;
    if (root !== document && root.classList && root.classList.contains("sheet")) {
      // scroll only the sheet; scrollIntoView would also move the page underneath
      var r = t.getBoundingClientRect(), sr = root.getBoundingClientRect();
      root.scrollTop += r.top - sr.top - root.clientHeight / 3;
    } else {
      t.scrollIntoView({block: "center"});
    }
    var tgt = t.classList.contains("anchor") ? (t.closest(".md, li, .thm, .p") || t) : t;
    tgt.classList.remove("flash"); void tgt.offsetWidth; tgt.classList.add("flash");
  }

  function popSheet() {
    var s = stack.pop();
    if (!s) return;
    s.el.remove();
    if (!stack.length) { document.documentElement.style.overflow = ""; window.scrollTo(0, baseScroll); }
    else stack[stack.length - 1].el.querySelector(".sheet-close").focus({preventScroll: true});
    renderBars();
  }

  function closeTo(depth) {
    // close sheets above `depth` through history so Back/Forward stay consistent
    var n = stack.length - depth;
    if (n > 0) history.go(-n);
  }

  window.addEventListener("popstate", function (ev) {
    var depth = (ev.state && typeof ev.state.depth === "number") ? ev.state.depth : 0;
    while (stack.length > depth) popSheet();
    if (stack.length < depth) restoreFromHash();
  });

  document.addEventListener("keydown", function (ev) {
    if (ev.key === "Escape" && stack.length) { ev.preventDefault(); closeTo(stack.length - 1); }
  });

  document.addEventListener("click", function (ev) {
    if (ev.defaultPrevented || ev.button !== 0 || ev.metaKey || ev.ctrlKey || ev.shiftKey || ev.altKey) return;
    var a = ev.target.closest("a");
    if (!a) return;
    if (a.classList.contains("sheet-page")) return;
    var href = a.getAttribute("href");
    if (!isLocal(href)) return;
    var inSheet = !!a.closest(".sheet");
    var opener = a.matches("a.ref, a.open-proof, a.thm-name, a.star-link, a.dag-link, a.res, .ch-card a, a.engine-pill, .deps a");
    if (!opener && !inSheet) return;
    ev.preventDefault();
    hidePeek();
    openSheet(href);
  });

  function restoreFromHash() {
    var m = /^#open=(.+)$/.exec(location.hash);
    if (!m) return;
    var urls = m[1].split("~").filter(Boolean);
    history.replaceState({depth: 0}, "", location.pathname);
    var chain = Promise.resolve();
    urls.forEach(function (u) {
      chain = chain.then(function () {
        var r = openSheet(u, {restoring: true});
        history.pushState({depth: stack.length}, "", "#open=" + stack.map(function (s) { return s.url; }).join("~"));
        return r;
      });
    });
  }

  // ---------------------------------------------------------- previews
  var peek = null, peekTimer = null, peekFor = null;
  function hidePeek() { clearTimeout(peekTimer); if (peek) { peek.remove(); peek = null; } peekFor = null; }
  document.addEventListener("mouseover", function (ev) {
    var a = ev.target.closest && ev.target.closest("a.ref[data-label], .deps a[data-label]");
    if (!a || a === peekFor || !matchMedia("(hover: hover)").matches) return;
    var href = a.getAttribute("href");
    if (!isLocal(href) || !/^r\./.test(pageOf(href).file)) return;
    hidePeek();
    peekFor = a;
    peekTimer = setTimeout(function () {
      var p = pageOf(href);
      fetchDoc(p.file).then(function (doc) {
        if (peekFor !== a) return;
        var thm = doc.querySelector("main.content .stmt-page > .thm");
        if (p.hash) {
          var t = doc.querySelector('[id="' + p.hash + '"]');
          if (t) thm = t.classList.contains("anchor") ? (t.closest(".md, li, .p") || thm) : t;
        }
        if (!thm) return;
        peek = document.createElement("div");
        peek.className = "peek";
        peek.appendChild(thm.cloneNode(true));
        var hint = document.createElement("div"); hint.className = "peek-hint"; hint.textContent = "Click to open with its proof";
        peek.appendChild(hint);
        document.body.appendChild(peek);
        var r = a.getBoundingClientRect();
        var x = Math.min(window.scrollX + r.left, window.scrollX + document.documentElement.clientWidth - peek.offsetWidth - 16);
        peek.style.left = Math.max(window.scrollX + 16, x) + "px";
        peek.style.top = (window.scrollY + r.bottom + 6) + "px";
        if (a.closest(".sheet")) { peek.style.position = "fixed"; peek.style.left = Math.max(16, Math.min(r.left, innerWidth - peek.offsetWidth - 16)) + "px"; peek.style.top = (r.bottom + 6) + "px"; }
        typeset(peek);
      });
    }, 380);
  });
  document.addEventListener("mouseout", function (ev) {
    if (peekFor && !peekFor.contains(ev.relatedTarget) && !(peek && peek.contains(ev.relatedTarget))) hidePeek();
  });

  // ---------------------------------------------------------- graphs on the home page
  var tip = document.getElementById("tip");
  var sky = document.querySelector(".sky");
  function showTip(el, text) {
    if (!tip || !sky) return;
    tip.textContent = text;
    tip.hidden = false;
    var r = el.getBoundingClientRect(), s = sky.getBoundingClientRect();
    tip.style.left = Math.min(r.left - s.left + 12, s.width - tip.offsetWidth - 4) + "px";
    tip.style.top = (r.top - s.top - 30) + "px";
  }
  function hideTip() { if (tip) tip.hidden = true; }
  function hot(label, engines, on) {
    document.querySelectorAll(".edge").forEach(function (e) {
      var match = (label && e.getAttribute("data-from") === label) || (engines && e.getAttribute("data-to") === engines);
      e.classList.toggle("hot", on && !!match);
    });
  }
  document.querySelectorAll(".star-link").forEach(function (a) {
    var f = function () { showTip(a, a.getAttribute("data-tip")); hot(a.getAttribute("data-label"), null, true); };
    a.addEventListener("mouseenter", f); a.addEventListener("focus", f);
    a.addEventListener("mouseleave", function () { hideTip(); hot(null, null, false); });
    a.addEventListener("blur", function () { hideTip(); hot(null, null, false); });
  });
  document.querySelectorAll(".hub-link").forEach(function (a) {
    var e = a.getAttribute("data-engine");
    var f = function () {
      showTip(a, a.getAttribute("data-tip")); hot(null, e, true);
      document.querySelectorAll(".star-link").forEach(function (s) {
        s.querySelector(".star").classList.toggle("hot", (" " + s.getAttribute("data-engines") + " ").indexOf(" " + e + " ") >= 0);
      });
    };
    var g = function () { hideTip(); hot(null, null, false); document.querySelectorAll(".star.hot").forEach(function (s) { s.classList.remove("hot"); }); };
    a.addEventListener("mouseenter", f); a.addEventListener("focus", f);
    a.addEventListener("mouseleave", g); a.addEventListener("blur", g);
  });
  document.querySelectorAll(".dag-link").forEach(function (a) {
    a.addEventListener("mouseenter", function () { showTip(a, a.getAttribute("data-tip")); });
    a.addEventListener("mouseleave", hideTip);
  });
  var vt = document.getElementById("view-top"), va = document.getElementById("view-all");
  function view(all) {
    document.getElementById("sky-top").hidden = all;
    document.getElementById("sky-all").hidden = !all;
    vt.classList.toggle("on", !all); va.classList.toggle("on", all);
    vt.setAttribute("aria-selected", String(!all)); va.setAttribute("aria-selected", String(all));
  }
  if (vt && va) { vt.addEventListener("click", function () { view(false); }); va.addEventListener("click", function () { view(true); }); }

  window.addEventListener("hashchange", function () {
    if (/^#open=/.test(location.hash) && !stack.length) restoreFromHash();
  });
  if (/^#open=/.test(location.hash)) restoreFromHash();
  else history.replaceState({depth: 0}, "", location.href);
})();
