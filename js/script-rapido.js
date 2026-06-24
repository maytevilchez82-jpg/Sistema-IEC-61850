var flatNodes = [],
  lnRecords = [];
var lnodeTypeIndex = {},
  doTypeIndex = {},
  daTypeIndex = {},
  enumTypeIndex = {},
  doiIndex = {};
var ldDescByLdInst = {};
var doiDescByLnDoKey = {};
var lnDescByLnKey = {};
var lnDescByLnClass = {};
var currentNodeMeta = null;
var treeSelectedNodes = {}; // Para almacenar nodos seleccionados del árbol
var cadenaExcludedRowKeys = {};
var datasetSelectedRecords = {};
var doTypeUtils = (typeof window !== "undefined" && window.doTypeUtils) || (typeof globalThis !== "undefined" && globalThis.doTypeUtils) || null;
var datasetSelectedOrder = [];
var datasetDisplayRecords = [];
var treeSelectedOrder = [];
var datasetFilterTimer = null;
var localNameCache = typeof WeakMap !== "undefined" ? new WeakMap() : null;
var datasetRenderToken = 0;

function setStatus(msg) {
  var el = document.getElementById("status");
  if (el) el.textContent = msg;
}

function esc(text) {
  if (text == null) return "";
  return String(text)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#39;");
}

function localName(node) {
  if (!node) return "";
  return node.localName || String(node.nodeName || "").replace(/^.*:/, "");
}

function normalizeName(value) {
  return String(value || "")
    .trim()
    .replace(/\s+/g, "")
    .toLowerCase();
}

function getEffectiveLdInst(ctx, attrs) {
  var context = ctx || {};
  var nodeAttrs = attrs || {};
  return (
    nodeAttrs.ldInst ||
    context.ldInst ||
    context.lDeviceInst ||
    ""
  );
}

function getDefaultLnContextForType(lnTypeId) {
  if (!lnTypeId || !Array.isArray(lnRecords) || !lnRecords.length) return {};
  for (var i = 0; i < lnRecords.length; i++) {
    var rec = lnRecords[i] || {};
    if (rec.LNodeType !== lnTypeId) continue;
    return {
      ldInst: rec.LDInst || "",
      prefix: rec.Prefix || "",
      lnClass: rec.LNClass || "",
      lnInst: rec.LNInst || "",
      lnType: rec.LNodeType || lnTypeId,
      lnDesc: rec.LNDesc || "",
      desc: rec.LNDesc || "",
    };
  }
  return {};
}

function isSameValue(left, right) {
  return normalizeName(left || "") === normalizeName(right || "");
}

function getDisplayFieldLabel(key) {
  return key;
}

function buildDatasetSearchText(record) {
  if (!record) return "";
  return [
    record.IED,
    record.DataSet,
    record.LDInst,
    record.Prefix,
    record.LNClass,
    record.LNInst,
    record.LNodeType,
    record.lnClassCID,
    record.DOsDefinidos,
    record.DOName,
    record.DOType,
    record.CDC,
    record.DAName,
    record.fc,
    record.Tag,
    record.CONCAT,
  ]
    .join(" ")
    .toLowerCase();
}

function getNormalizedToken(value) {
  return String(value || "")
    .trim()
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "-")
    .replace(/^-+|-+$/g, "");
}

function getFcBadgeClass(fc) {
  var token = getNormalizedToken(fc);
  if (!token) return "badge-fc badge-fc-default";
  return "badge-fc badge-fc-" + token;
}

function getTagBadgeClass(tag) {
  var token = getNormalizedToken(tag);
  if (!token) return "badge-tag badge-tag-default";
  return "badge-tag badge-tag-" + token.replace(/_synth/g, "");
}

function getLdDescByInst(inst) {
  var value = String(inst || "").trim();
  if (!value) return "";
  return ldDescByLdInst[value] || "";
}

function levenshteinDistance(a, b) {
  var i, j, prev, current, cost;
  if (!a) return b ? b.length : 0;
  if (!b) return a.length;
  prev = new Array(b.length + 1);
  for (j = 0; j <= b.length; j++) prev[j] = j;
  for (i = 1; i <= a.length; i++) {
    current = [i];
    for (j = 1; j <= b.length; j++) {
      cost = a.charAt(i - 1) === b.charAt(j - 1) ? 0 : 1;
      current[j] = Math.min(
        prev[j] + 1,
        current[j - 1] + 1,
        prev[j - 1] + cost
      );
    }
    prev = current;
  }
  return prev[b.length];
}

function nameSimilarity(a, b) {
  var left = normalizeName(a);
  var right = normalizeName(b);
  if (!left || !right) return 0;
  if (left === right) return 1;
  if (left.indexOf(right) !== -1 || right.indexOf(left) !== -1) return 0.85;
  var distance = levenshteinDistance(left, right);
  var maxLen = Math.max(left.length, right.length);
  return maxLen ? Math.max(0, 1 - distance / maxLen) : 0;
}

function findBestFcdaMatch(doName, lnType, ctx, records, doTypeId) {
  if (!doName || !Array.isArray(records) || !records.length) return null;
  var candidates = [];
  var targetName = normalizeName(doName);
  var targetDoType = normalizeName(doTypeId || "");
  var targetLdInst = getEffectiveLdInst(ctx);
  records.forEach(function (rec) {
    if (!rec || String(rec.Tag || "").toUpperCase() !== "FCDA") return;

    var recName = normalizeName(rec.DOName || "");
    var recDoType = normalizeName(rec.DOType || "");
    var score = 0;
    var sim = recName === targetName ? 1 : nameSimilarity(rec.DOName, doName);

    if (recName === targetName) score += 1.1;
    else if (sim >= 0.25) score += 0.35 + sim * 0.55;

    if (targetDoType && recDoType === targetDoType) score += 0.95;
    else if (targetDoType && recDoType) score -= 0.1;

    if (lnType && rec.LNodeType && normalizeName(rec.LNodeType) === normalizeName(lnType)) score += 0.6;
    else if (lnType && rec.LNodeType) score += 0.15;

    if (ctx && ctx.lnClass && rec.LNClass && normalizeName(rec.LNClass) === normalizeName(ctx.lnClass)) score += 0.25;
    else if (ctx && ctx.lnClass && rec.LNClass) score += 0.08;

    if (ctx && ctx.prefix && rec.Prefix && normalizeName(rec.Prefix) === normalizeName(ctx.prefix)) score += 0.15;
    else if (ctx && ctx.prefix && rec.Prefix) score += 0.04;

    if (ctx && ctx.lnInst && rec.LNInst && normalizeName(rec.LNInst) === normalizeName(ctx.lnInst)) score += 0.15;
    else if (ctx && ctx.lnInst && rec.LNInst) score += 0.04;

    if (targetLdInst && rec.LDInst && isSameValue(rec.LDInst, targetLdInst)) score += 2.5;
    else if (targetLdInst && rec.LDInst) score -= 0.35;

    if (rec.DOType) score += 0.03;
    if (rec.DAName) score += 0.02;

    candidates.push({ rec: rec, score: score });
  });

  candidates.sort(function (a, b) {
    return b.score - a.score || String(a.rec.DOName || "").localeCompare(String(b.rec.DOName || ""));
  });

  if (!candidates.length || candidates[0].score < 0.18) return null;
  return candidates[0];
}

function findMatchingFcdaRecords(doName, lnType, ctx, records, doTypeId) {
  if (!doName || !Array.isArray(records) || !records.length) return [];
  var targetDoName = normalizeName(doName);
  var targetLnType = normalizeName(lnType || "");
  var targetDoType = normalizeName(doTypeId || "");
  var targetLdInst = getEffectiveLdInst(ctx);
  var out = [];

  records.forEach(function (rec) {
    if (!rec || String(rec.Tag || "").toUpperCase() !== "FCDA") return;
    if (normalizeName(rec.DOName || "") !== targetDoName) return;

    if (targetLnType && rec.LNodeType && normalizeName(rec.LNodeType) !== targetLnType) return;
    if (targetDoType && rec.DOType && normalizeName(rec.DOType) !== targetDoType) return;

    var sameLdInst = !!(targetLdInst && rec.LDInst && isSameValue(rec.LDInst, targetLdInst));
    if (targetLdInst && rec.LDInst && !sameLdInst) return;
    if (!sameLdInst && ctx && ctx.prefix && rec.Prefix && normalizeName(rec.Prefix) !== normalizeName(ctx.prefix)) return;
    if (!sameLdInst && ctx && ctx.lnClass && rec.LNClass && normalizeName(rec.LNClass) !== normalizeName(ctx.lnClass)) return;
    if (!sameLdInst && ctx && ctx.lnInst && rec.LNInst && normalizeName(rec.LNInst) !== normalizeName(ctx.lnInst)) return;

    out.push(rec);
  });

  out.sort(function (a, b) {
    return String(a.DAName || "").localeCompare(String(b.DAName || "")) ||
      String(a.fc || "").localeCompare(String(b.fc || ""));
  });

  return out;
}

function findNamedEntry(list, name) {
  if (!list || !list.length) return null;
  var target = normalizeName(name);
  for (var i = 0; i < list.length; i++) {
    if (normalizeName(list[i].name) === target) return list[i];
  }
  return null;
}

function getDoiDescription(doName) {
  if (!doName || !doiIndex) return "";
  return doiIndex[doName] || "";
}

function buildLnDoKey(ldInst, prefix, lnClass, lnInst, doName) {
  return [
    normalizeName(ldInst || ""),
    normalizeName(prefix || ""),
    normalizeName(lnClass || ""),
    normalizeName(lnInst || ""),
    normalizeName(doName || "")
  ].join("|");
}

function buildLnKey(ldInst, prefix, lnClass, lnInst) {
  return [
    normalizeName(ldInst || ""),
    normalizeName(prefix || ""),
    normalizeName(lnClass || ""),
    normalizeName(lnInst || "")
  ].join("|");
}

function getDoiDescriptionForContext(doName, fields, attrs, ctx) {
  fields = fields || {};
  attrs = attrs || {};
  ctx = ctx || {};
  if (!doName) return "";

  var ldInst = fields.ldInst || attrs.ldInst || ctx.ldInst || ctx.lDeviceInst || "";
  var prefix = fields.prefix || attrs.prefix || ctx.prefix || "";
  var lnClass = fields.lnClass || attrs.lnClass || attrs["lnClass (CID)"] || ctx.lnClass || "";
  var lnInst = fields.lnInst || attrs.lnInst || attrs.inst || ctx.lnInst || "";
  var lnType = fields.lnType || attrs.lnType || attrs["lnType (CID)"] || ctx.lnType || "";
  var key = buildLnDoKey(ldInst, prefix, lnClass, lnInst, doName);
  if (doiDescByLnDoKey && doiDescByLnDoKey[key]) return doiDescByLnDoKey[key];
  if (Array.isArray(lnRecords) && lnRecords.length) {
    var bestMatch = findBestFcdaMatch(doName, lnType, {
      ldInst: ldInst,
      prefix: prefix,
      lnClass: lnClass,
      lnInst: lnInst,
    }, lnRecords, "");
    if (bestMatch && bestMatch.rec && bestMatch.rec.DODesc) {
      return bestMatch.rec.DODesc;
    }
  }
  return getDoiDescription(doName);
  if (lnClassValue) cidAttrs.push(["lnClass", lnClassValue, ""]);
}

function getDoDescriptionFromLnType(lnType, doName, fields, attrs, ctx) {
  var contextualDesc = getDoiDescriptionForContext(doName, fields || {}, attrs || {}, ctx || {});
  if (contextualDesc) return contextualDesc;
  return getDoiDescription(doName);
}

function normalizeDescriptionValue(value) {
  var text = String(value || "").trim();
  return text ? text : "No definido";
}

function buildCompositeDescription(ldDesc, lnDesc, doDesc) {
  return [
    "LD Desc (Logical Device Description): " + normalizeDescriptionValue(ldDesc),
    "LN Desc (Logical Node Description): " + normalizeDescriptionValue(lnDesc),
    "DO Desc (Data Object Description): " + normalizeDescriptionValue(doDesc)
  ].join(" // ");
}

function getDoDescriptionForSelection(node, fields, attrs, ctx) {
  attrs = attrs || {};
  var doName = (fields && fields.doName) || attrs.doName || attrs.name || "";
  var context = ctx || (node && node.ctx) || {};
  var targetDoName = normalizeName(doName);
  var sourceDoName = normalizeName(attrs.doName || attrs.DOName || attrs.name || "");
  var directDesc = attrs.doDesc || attrs.DODesc || attrs["DO desc"] || attrs.desc || "";
  if (directDesc && targetDoName && sourceDoName && targetDoName === sourceDoName) return directDesc;
  if (directDesc && !targetDoName) return directDesc;
  var doiDesc = getDoiDescriptionForContext(doName, fields, attrs, context);
  if (doiDesc) return doiDesc;
  var lnType = (fields && fields.lnType) || attrs["lnType (CID)"] || attrs.lnType || "";
  return getDoDescriptionFromLnType(lnType, doName);
}

function getLnTypeDoDescriptionList(fields, attrs, ctx) {
  fields = fields || {};
  attrs = attrs || {};
  ctx = ctx || {};

  var lnType = fields.lnType || attrs.lnType || attrs["lnType (CID)"] || ctx.lnType || "";
  if (!lnType || !lnodeTypeIndex[lnType] || !lnodeTypeIndex[lnType].dos || !lnodeTypeIndex[lnType].dos.length) {
    return [];
  }

  var target = {
    ldInst: fields.ldInst || attrs.ldInst || ctx.ldInst || ctx.lDeviceInst || "",
    prefix: fields.prefix || attrs.prefix || ctx.prefix || "",
    lnClass: fields.lnClass || attrs.lnClass || attrs["lnClass (CID)"] || ctx.lnClass || "",
    lnInst: fields.lnInst || attrs.lnInst || attrs.inst || ctx.lnInst || "",
  };
  var descriptions = [];

  lnodeTypeIndex[lnType].dos.forEach(function (doEntry) {
    var doName = doEntry.name || "";
    if (!doName) return;

    var matches = findMatchingFcdaRecords(doName, lnType, target, lnRecords, doEntry.type || "");
    var bestDesc = matches.length ? (matches[0].DODesc || matches[0].Description || "") : "";
    if (!bestDesc) {
      bestDesc = getDoiDescriptionForContext(doName, Object.assign({}, target, { lnType: lnType, doName: doName }), attrs, ctx);
    }
    if (bestDesc) descriptions.push(doName + ": " + bestDesc);
  });

  return descriptions;
}

function getCidDescriptionFields(fields, attrs, ctx) {
  fields = fields || {};
  attrs = attrs || {};
  ctx = ctx || {};

  var target = {
    ldInst: fields.ldInst || attrs.ldInst || ctx.ldInst || ctx.lDeviceInst || "",
    prefix: fields.prefix || attrs.prefix || ctx.prefix || "",
    lnClass: fields.lnClass || attrs.lnClass || attrs["lnClass (CID)"] || ctx.lnClass || "",
    lnInst: fields.lnInst || attrs.lnInst || attrs.inst || ctx.lnInst || "",
    lnType: fields.lnType || attrs.lnType || attrs["lnType (CID)"] || ctx.lnType || "",
    doName: fields.doName || attrs.doName || attrs.name || "",
  };

  var matches = [];
  for (var i = 0; i < lnRecords.length; i++) {
    var rec = lnRecords[i] || {};
    var score = 0;
    if (target.ldInst && normalizeName(rec.LDInst || "") === normalizeName(target.ldInst)) score += 5;
    if (target.prefix && normalizeName(rec.Prefix || "") === normalizeName(target.prefix)) score += 4;
    if (target.lnInst && normalizeName(rec.LNInst || "") === normalizeName(target.lnInst)) score += 4;
    if (target.lnType && normalizeName(rec.LNodeType || "") === normalizeName(target.lnType)) score += 4;
    if (target.doName && normalizeName(rec.DOName || "") === normalizeName(target.doName)) score += 3;
    if (normalizeName(rec.LNClass || "") === normalizeName(target.lnClass || "")) score += 2;

    matches.push({ rec: rec, score: score });
  }

  matches.sort(function (a, b) { return b.score - a.score; });
  var best = matches.length ? matches[0].rec : null;
  var lnKey = buildLnKey(target.ldInst, target.prefix, target.lnClass, target.lnInst);
  var lnDescFromKey = (lnKey && lnDescByLnKey[lnKey]) || "";
  var lnDescFromClass = target.lnClass ? (lnDescByLnClass[normalizeName(target.lnClass)] || "") : "";
  var ldDescFromInst = getLdDescByInst(target.ldInst);
  var doDescFromDoi = "";
  if (target.doName) {
    doDescFromDoi = getDoDescriptionForSelection(null, fields, attrs, ctx);
  } else if (target.lnType && lnodeTypeIndex[target.lnType] && lnodeTypeIndex[target.lnType].dos && lnodeTypeIndex[target.lnType].dos.length) {
    doDescFromDoi = getLnTypeDoDescriptionList(fields, attrs, ctx).join(" · ");
  } else {
    doDescFromDoi = getDoDescriptionForSelection(null, fields, attrs, ctx);
  }
  var hasLdReference = !!(target.ldInst || attrs.ldInst || ctx.ldInst || ctx.lDeviceInst);

  return {
    ldDesc: hasLdReference ? (ldDescFromInst || ctx.ldDesc || attrs.ldDesc || (best && best.LDDesc) || "") : "",
    lnDesc: lnDescFromKey || lnDescFromClass || ctx.lnDesc || ctx.desc || attrs.lnDesc || (best && best.LNDesc) || "",
    doDesc: doDescFromDoi || (best && best.DODesc) || "",
  };
}

function buildSelectionCidDescription(node, fields, attrs, ctx) {
  ctx = ctx || {};
  attrs = attrs || {};
  var cidDesc = getCidDescriptionFields(fields, attrs, ctx);
  var ldDesc = cidDesc.ldDesc;
  var lnDesc = cidDesc.lnDesc;
  var doDesc = cidDesc.doDesc;
  return buildCompositeDescription(ldDesc, lnDesc, doDesc);
}

function findAllByLocalName(root, name) {
  var result = [];
  if (!root || !name) return result;
  var cacheKey = String(name || "");

  if (localNameCache) {
    var cachedByRoot = localNameCache.get(root);
    if (!cachedByRoot) {
      // Optimización: la primera vez que se consulta este root, recorremos
      // TODO el documento una sola vez y clasificamos cada nodo por su
      // localName. Así, buscar 7-8 tags distintos (LNodeType, DOType,
      // DAType, EnumType, DOI, LN, LDevice...) sobre el mismo xmlDoc cuesta
      // un solo recorrido en vez de uno por cada tag.
      cachedByRoot = {};
      var allNodes = root.getElementsByTagName("*");
      for (var i = 0; i < allNodes.length; i++) {
        var n = allNodes[i];
        var ln = localName(n);
        if (!cachedByRoot[ln]) cachedByRoot[ln] = [];
        cachedByRoot[ln].push(n);
      }
      localNameCache.set(root, cachedByRoot);
    }
    return cachedByRoot[cacheKey] || [];
  }

  var nodes = root.getElementsByTagName("*");
  for (var j = 0; j < nodes.length; j++) {
    if (localName(nodes[j]) === cacheKey) result.push(nodes[j]);
  }
  return result;
}

function collectAttributes(node) {
  var attrs = {};
  if (!node || !node.attributes) return attrs;
  for (var i = 0; i < node.attributes.length; i++) {
    var attr = node.attributes[i];
    if (attr && attr.name) attrs[attr.name] = attr.value;
  }
  return attrs;
}

function hasAttrs(node) {
  if (!node) return false;
  if (node.attributes && node.attributes.length > 0) return true;
  for (var i = 0; i < node.children.length; i++) {
    if (hasAttrs(node.children[i])) return true;
  }
  return false;
}

function hasTextValue(node) {
  if (!node || !node.childNodes) return false;
  for (var i = 0; i < node.childNodes.length; i++) {
    var child = node.childNodes[i];
    if (child && (child.nodeType === 3 || child.nodeType === 4)) {
      if (String(child.textContent || "").trim()) return true;
    }
  }
  return false;
}

function getTextValue(node) {
  if (!node || !node.childNodes) return "";
  var text = [];
  for (var i = 0; i < node.childNodes.length; i++) {
    var child = node.childNodes[i];
    if (child && (child.nodeType === 3 || child.nodeType === 4)) {
      var value = String(child.textContent || "").trim();
      if (value) text.push(value);
    }
  }
  return text.join(" ");
}

function buildDataModelIndex(xmlDoc) {
  lnodeTypeIndex = {};
  doTypeIndex = {};
  daTypeIndex = {};
  enumTypeIndex = {};
  doiIndex = {};
  ldDescByLdInst = {};
  doiDescByLnDoKey = {};
  lnDescByLnKey = {};
  lnDescByLnClass = {};

  findAllByLocalName(xmlDoc, "LNodeType").forEach(function (lnt) {
    var id = lnt.getAttribute("id") || "";
    var dos = [];
    var childDos = lnt.children;
    for (var i = 0; i < childDos.length; i++) {
      if (localName(childDos[i]) === "DO") {
        dos.push({
          name: childDos[i].getAttribute("name") || "",
          type: childDos[i].getAttribute("type") || "",
          attrs: collectAttributes(childDos[i]),
        });
      }
    }
    lnodeTypeIndex[id] = {
      lnClass: lnt.getAttribute("lnClass") || "",
      dos: dos,
    };
  });

  findAllByLocalName(xmlDoc, "DOType").forEach(function (dt) {
    var id = dt.getAttribute("id") || "";
    var das = [],
      sdos = [];
    var childNodes = dt.children;
    for (var i = 0; i < childNodes.length; i++) {
      var child = childNodes[i];
      if (localName(child) === "DA") {
        das.push({
          name: child.getAttribute("name") || "",
          fc: child.getAttribute("fc") || "",
          bType: child.getAttribute("bType") || "",
          type: child.getAttribute("type") || "",
          attrs: collectAttributes(child),
        });
      } else if (localName(child) === "SDO") {
        sdos.push({
          name: child.getAttribute("name") || "",
          type: child.getAttribute("type") || "",
        });
      }
    }
    doTypeUtils && doTypeUtils.appendIndexedDefinition
      ? doTypeUtils.appendIndexedDefinition(doTypeIndex, id, {
          cdc: dt.getAttribute("cdc") || "",
          das: das,
          sdos: sdos,
        })
      : (doTypeIndex[id] = {
          cdc: dt.getAttribute("cdc") || "",
          das: das,
          sdos: sdos,
        });
  });

  findAllByLocalName(xmlDoc, "DAType").forEach(function (dat) {
    var id = dat.getAttribute("id") || "";
    var das = [];
    var bdas = [];
    var childNodes = dat.children;
    for (var i = 0; i < childNodes.length; i++) {
      var child = childNodes[i];
      if (localName(child) === "DA") {
        das.push({
          name: child.getAttribute("name") || "",
          fc: child.getAttribute("fc") || "",
          bType: child.getAttribute("bType") || "",
          type: child.getAttribute("type") || "",
          attrs: collectAttributes(child),
        });
      } else if (localName(child) === "BDA") {
        bdas.push({
          name: child.getAttribute("name") || "",
          fc: child.getAttribute("fc") || "",
          bType: child.getAttribute("bType") || "",
          type: child.getAttribute("type") || "",
          attrs: collectAttributes(child),
        });
      }
    }
    daTypeIndex[id] = { das: das, bdas: bdas };
  });

  findAllByLocalName(xmlDoc, "EnumType").forEach(function (et) {
    var id = et.getAttribute("id") || "";
    var vals = [];
    var childNodes = et.children;
    for (var i = 0; i < childNodes.length; i++) {
      var child = childNodes[i];
      if (localName(child) === "EnumVal") {
        vals.push({
          ord: child.getAttribute("ord") || "",
          text: (child.textContent || "").trim(),
        });
      }
    }
    enumTypeIndex[id] = { vals: vals };
  });

  function findAncestor(node, name) {
    var current = node && node.parentNode ? node.parentNode : null;
    while (current) {
      if (localName(current) === name) return current;
      current = current.parentNode;
    }
    return null;
  }

  findAllByLocalName(xmlDoc, "DOI").forEach(function (doi) {
    var name = doi.getAttribute("name") || "";
    var desc = String(doi.getAttribute("desc") || "").trim();
    if (name) {
      doiIndex[name] = desc;
    }

    if (!name || !desc) return;

    var ln = findAncestor(doi, "LN") || findAncestor(doi, "LN0");
    if (!ln) return;

    var lDevice = findAncestor(doi, "LDevice");
    var ldInst = lDevice && lDevice.getAttribute ? (lDevice.getAttribute("inst") || "") : "";
    var prefix = ln.getAttribute ? (ln.getAttribute("prefix") || "") : "";
    var lnClass = ln.getAttribute ? (ln.getAttribute("lnClass") || "") : "";
    var lnInst = ln.getAttribute ? (ln.getAttribute("inst") || "") : "";
    var key = buildLnDoKey(ldInst, prefix, lnClass, lnInst, name);
    if (key && !doiDescByLnDoKey[key]) doiDescByLnDoKey[key] = desc;
  });

  findAllByLocalName(xmlDoc, "LN").concat(findAllByLocalName(xmlDoc, "LN0")).forEach(function (ln) {
    if (!ln || !ln.getAttribute) return;

    var lnDesc = String(ln.getAttribute("desc") || "").trim();
    if (!lnDesc) return;

    var lDevice = findAncestor(ln, "LDevice");
    var ldInst = lDevice && lDevice.getAttribute ? (lDevice.getAttribute("inst") || "") : "";
    var prefix = ln.getAttribute("prefix") || "";
    var lnClass = ln.getAttribute("lnClass") || "";
    var lnInst = ln.getAttribute("inst") || "";
    var lnKey = buildLnKey(ldInst, prefix, lnClass, lnInst);
    var lnClassKey = normalizeName(lnClass || "");

    if (lnKey && !lnDescByLnKey[lnKey]) lnDescByLnKey[lnKey] = lnDesc;
    if (lnClassKey && !lnDescByLnClass[lnClassKey]) lnDescByLnClass[lnClassKey] = lnDesc;
  });

  findAllByLocalName(xmlDoc, "LDevice").forEach(function (lDevice) {
    var inst = lDevice.getAttribute ? (lDevice.getAttribute("inst") || "") : "";
    if (!inst) return;

    var fromLd = lDevice.getAttribute ? (lDevice.getAttribute("desc") || "") : "";
    var resolved = String(fromLd || "").trim();
    if (resolved) ldDescByLdInst[inst] = resolved;
  });
}

function applyExcelAutoFit(ws, minWidth) {
  minWidth = minWidth || 10;
  ws.properties = ws.properties || {};
  ws.properties.defaultRowHeight = 15;

  ws.columns.forEach(function (column) {
    if (!column) return;
    var maxLength = minWidth;
    column.eachCell({ includeEmpty: true }, function (cell) {
      var value = cell.value;
      if (value == null) return;
      var text = String(value);
      if (text.length > maxLength) maxLength = text.length;
    });
    column.width = Math.min(Math.max(maxLength + 2, minWidth), 80);
    column.alignment = { horizontal: "left", vertical: "top", wrapText: true };
  });
}

function applyExcelFrame(ws, color) {
  color = color || "FF334155";
  ws.eachRow({ includeEmpty: true }, function (row) {
    row.eachCell({ includeEmpty: true }, function (cell) {
      cell.border = {
        top: { style: "thin", color: { argb: color } },
        left: { style: "thin", color: { argb: color } },
        bottom: { style: "thin", color: { argb: color } },
        right: { style: "thin", color: { argb: color } },
      };
    });
  });
}

function buildRef(ctx) {
  ctx = ctx || {};
  var ln = (ctx.prefix || "") + (ctx.lnClass || "") + (ctx.lnInst || "");
  var parts = [];
  var ldInst = getEffectiveLdInst(ctx);
  if (ldInst) parts.push(ldInst);
  var lndo = ln + (ctx.doName ? "." + ctx.doName : "");
  if (lndo) parts.push(lndo);
  return parts.join("/");
}

function getEnumTypeValues(typeId) {
  var enumType = enumTypeIndex[typeId];
  if (!enumType || !enumType.vals.length) return "";
  return enumType.vals
    .map(function (val) {
      return (val.ord ? val.ord + " - " : "") + (val.text || "");
    })
    .join(", ");
}

function section(title, rows) {
  var html = "";
  html += '<div class="detail-section">';
  html += '<div class="detail-section-title">' + esc(title) + "</div>";
  rows.forEach(function (row) {
    var key = getDisplayFieldLabel(row[0]);
    var value = row[1];
    var cls = row[2] || "";
    html +=
      '<div class="detail-attr-row"><span class="detail-attr-key">' +
      esc(key) +
      '</span><span class="detail-attr-val ' +
      cls +
      '">' +
      esc(value) +
      "</span></div>";
  });
  html += "</div>";
  return html;
}

function filterNonEmptyRows(rows) {
  return (rows || []).filter(function (row) {
    return String(row[1] || "").trim() !== "";
  });
}

function extraSection(title, rows) {
  var html = "";
  html += '<div class="detail-section" style="border-color:#334155;background:#111827">';
  html += '<div class="detail-section-title" style="color:#93c5fd">' + esc(title) + "</div>";
  rows.forEach(function (row) {
    var key = getDisplayFieldLabel(row[0]);
    var value = row[1];
    var cls = row[2] || "";
    html +=
      '<div class="detail-attr-row"><span class="detail-attr-key" style="color:#60a5fa">' +
      esc(key) +
      '</span><span class="detail-attr-val ' +
      cls +
      '" style="color:#e2e8f0">' +
      esc(value) +
      "</span></div>";
  });
  html += "</div>";
  return html;
}

function daTable(das) {
  var html = "";
  das.forEach(function (da) {
    html += '<div class="da-row">';
    html += '<span class="da-name">' + esc(da.name) + "</span>";
    html += '<span class="da-fc">' + esc(da.fc || "") + "</span>";
    html += '<span class="da-btype">' + esc(da.bType || "") + "</span>";
    var enumVals = getEnumTypeValues(da.type || "");
    html +=
      '<span class="da-type">' +
      esc(da.type || "") +
      (enumVals ? " (" + esc(enumVals) + ")" : "") +
      "</span>";
    var extraAttrs = Object.keys(da.attrs || {}).filter(function (key) {
      return !["name", "fc", "bType", "type"].includes(key);
    });
    if (extraAttrs.length) {
      html += '<span class="da-extra">' + esc(extraAttrs.map(function (key) {
        return key + "=" + String(da.attrs[key] || "");
      }).join(" | ")) + "</span>";
    }
    html += "</div>";
  });
  return html;
}

function doCard(doEntry, doTypeDef, cdc, options) {
  var html = "";
  options = options || {};
  var doiDesc = getDoiDescriptionForContext(
    doEntry.name,
    {
      ldInst: options.ldInst || "",
      prefix: options.prefix || "",
      lnClass: options.lnClass || "",
      lnInst: options.lnInst || "",
      lnType: options.lnType || "",
    },
    options.attrs || {},
    options.ctx || {}
  ) || getDoiDescription(doEntry.name);
  html += '<div class="do-card">';
  html += '<div class="do-card-header">';
  html += '<span class="do-card-name">' + esc(doEntry.name) + "</span>";
  html +=
    '<span class="do-card-type">DOType: ' +
    esc(doEntry.type) +
    ' (definido por CID)</span>';
  html += '<span class="do-card-cdc">' + esc(cdc) + "</span>";
  html += '<span class="chevron">›</span>';
  html += "</div>";
  if (doiDesc) {
    html += '<div class="do-card-desc" style="padding:8px 12px;background:#0f172a;border-top:1px solid #1e293b;font-size:12px;color:#cbd5e1">';
    html += '<span style="color:#60a5fa;font-weight:600">DO Desc (Data Object Description):</span> ' + esc(doiDesc);
    html += '</div>';
  }
  html += '<div class="do-card-body">';
  if (doTypeDef) html += daTable(doTypeDef.das);
  html += "</div>";
  html += "</div>";
  return html;
}

function renderBdaTreeRows(bdas, level) {
  var html = "";
  var depth = level || 0;
  (bdas || []).forEach(function (bda) {
    var nestedTypeId = bda && bda.type ? bda.type : "";
    var nestedTypeDef = nestedTypeId && daTypeIndex[nestedTypeId] ? daTypeIndex[nestedTypeId] : null;
    var nestedBdas = nestedTypeDef && nestedTypeDef.bdas ? nestedTypeDef.bdas : [];
    var enumVals = getEnumTypeValues(nestedTypeId || "");
    var leftPad = 10 + depth * 18;

    html += '<div class="da-row" style="padding-left:' + leftPad + 'px">';
    html += '<span class="da-name" style="color:#93c5fd">' + esc(bda && bda.name ? bda.name : "") + "</span>";
    html += '<span class="da-fc">' + esc(bda && bda.fc ? bda.fc : "") + "</span>";
    html += '<span class="da-btype">' + esc(bda && bda.bType ? bda.bType : "") + "</span>";
    html += '<span class="da-type">' + esc(nestedTypeId) + (enumVals ? " (" + esc(enumVals) + ")" : "") + "</span>";
    if (depth > 0) {
      html += '<span class="tag-badge" style="background:#1e293b;color:#94a3b8">Nivel ' + esc(String(depth + 1)) + "</span>";
    }
    html += "</div>";
  });
  return html;
}

function renderDetail(meta) {
  var c = document.getElementById("detail-container");
  if (!c) return;
  if (!meta) {
    c.innerHTML =
      '<div class="empty-msg"><i class="fa fa-mouse-pointer" style="font-size:24px;margin-bottom:8px;display:block;color:#334155"></i>Selecciona un nodo del árbol</div>';
    return;
  }

  var tag = meta.tag || "";
  var attrs = meta.attrs || {};
  var html = "";
  var tagClass = "tag-" + tag.toLowerCase().replace(/_synth/g, "");

  html += '<div style="display:flex;align-items:center;gap:8px;margin-bottom:14px">';
  html +=
    '<span class="tag-badge ' +
    tagClass +
    '" style="font-size:13px;padding:4px 12px">' +
    esc(tag.replace(/_SYNTH/g, "")) +
    "</span>";
  if (attrs.name)
    html +=
      '<span style="font-size:16px;font-weight:700;color:#e2e8f0">' +
      esc(attrs.name) +
      "</span>";
  html += "</div>";

  if (tag === "LDevice") {
    html += section("Logical Device", [
      ["inst", attrs.inst || attrs.ldInst || "", ""],
      ["LD Desc (Logical Device Description)", attrs.desc || meta.ctx && meta.ctx.ldDesc || "", ""],
    ]);
    return;
  }

  if (tag === "LN" || tag === "LN0" || tag === "LN_SYNTH") {
    var prefix = attrs.prefix || "";
    var lnClass = attrs.lnClass || attrs["lnClass (CID)"] || "";
    var inst = attrs.inst || attrs.lnInst || "";
    var iedName = meta.ctx && meta.ctx.iedName ? meta.ctx.iedName : (attrs.iedName || "");
    var ldInst = meta.ctx && (meta.ctx.ldInst || meta.ctx.lDeviceInst) ? (meta.ctx.ldInst || meta.ctx.lDeviceInst) : (attrs.ldInst || "");
    var lnType = attrs.lnType || "";
    var lnIdentifier = [prefix, lnClass, inst].filter(function (v) { return v; }).join("");
    var lnt = lnodeTypeIndex[lnType] || null;
    var cidLnClass = lnt && lnt.lnClass ? lnt.lnClass : (attrs["lnClass (CID)"] || lnClass || "");
    var lnCidDesc = getCidDescriptionFields({
      ldInst: ldInst,
      prefix: prefix,
      lnClass: lnClass,
      lnInst: inst,
      lnType: lnType,
    }, attrs, meta.ctx || {});
    var doDescRows = [];
    if (lnt && lnt.dos && lnt.dos.length) {
      lnt.dos.forEach(function (doEntry) {
        var doDesc = getDoiDescriptionForContext(
          doEntry.name,
          {
            ldInst: ldInst,
            prefix: prefix,
            lnClass: lnClass,
            lnInst: inst,
            lnType: lnType,
          },
          attrs,
          meta.ctx || {}
        ) || getDoiDescription(doEntry.name);
        doDescRows.push([doEntry.name || "DO", normalizeDescriptionValue(doDesc), ""]);
      });
    } else if (lnCidDesc.doDesc) {
      doDescRows.push(["DO Desc", normalizeDescriptionValue(lnCidDesc.doDesc), ""]);
    }

    html += '<div style="margin-bottom:16px;padding:12px;background:#1e293b;border-left:4px solid #60a5fa;border-radius:4px">';
    html += '<div style="font-size:12px;color:#94a3b8;margin-bottom:6px">Identificador del Nodo Lógico</div>';
    html += '<div style="font-size:20px;font-weight:700;color:#60a5fa;font-family:monospace">' + esc(lnIdentifier) + '</div>';
    html += '</div>';

    html +=
      section("Nodo Lógico", [
        ["IED", iedName, "highlight"],
        ["LDInst", ldInst, ""],
        ["prefix", prefix, ""],
        ["lnClass", lnClass, ""],
        ["inst", inst, ""],
        ["lnType", lnType, "blue"],
        ["lnClass (CID)", cidLnClass, ""],
        ["LD Desc (Logical Device Description)", (meta.ctx && meta.ctx.ldDesc) || attrs.ldDesc || "", ""],
        ["LN Desc (Logical Node Description)", attrs.desc || (meta.ctx && meta.ctx.lnDesc) || "", ""],
      ]);
    html += extraSection("Descripción CID", [
      ["LD Desc (Logical Device Description)", normalizeDescriptionValue(lnCidDesc.ldDesc), ""],
      ["LN Desc (Logical Node Description)", normalizeDescriptionValue(lnCidDesc.lnDesc), ""],
    ]);
    if (doDescRows.length) {
      html += extraSection("DO Desc (Data Object Description)", doDescRows);
    } else {
      html += extraSection("DO Desc (Data Object Description)", [
        ["DO Desc", normalizeDescriptionValue(lnCidDesc.doDesc), ""],
      ]);
    }
    if (lnt) {
      html += '<div class="detail-section">';
      html +=
        '<div class="detail-section-title">Data Objects (' +
        lnt.dos.length +
        ") — desde DataTypeTemplates</div>";
      lnt.dos.forEach(function (doEntry) {
        var doTypeDef = doTypeUtils && doTypeUtils.getDoTypeDefinition
          ? doTypeUtils.getDoTypeDefinition(doTypeIndex, doEntry.type)
          : (doTypeIndex[doEntry.type] || null);
        var cdc = doTypeDef ? doTypeDef.cdc : "";
        html += doCard(doEntry, doTypeDef, cdc, {
          ldInst: ldInst,
          prefix: prefix,
          lnClass: lnClass,
          lnInst: inst,
          lnType: lnType,
          attrs: attrs,
          ctx: meta.ctx || {},
        });
      });
      html += "</div>";
      var doNames = (lnt && lnt.dos ? lnt.dos.map(function (entry) { return entry.name || ""; }).filter(Boolean) : []);
      html += extraSection("Detalles adicionales", [
        ["Identificador LN", lnIdentifier, ""],
        ["LNodeType", lnType || "", "blue"],
        ["LD Desc (Logical Device Description)", (meta.ctx && meta.ctx.ldDesc) || attrs.ldDesc || "", ""],
        ["DOName", doNames.length ? doNames.join(" · ") : "", "highlight"],
        ["lnClass (CID)", cidLnClass || "", ""],
      ]);
    }
  } else if (tag === "LNodeType" || tag === "LNODETYPE") {
    var lnTypeId = attrs.id || attrs.lnType || attrs.name || "";
    var lntDef = lnTypeId ? lnodeTypeIndex[lnTypeId] || null : null;
    var lnodeDoCount = lntDef && lntDef.dos ? lntDef.dos.length : 0;

    html +=
      section("LNodeType", [
        ["id", lnTypeId, "blue"],
        ["lnClass", (lntDef && lntDef.lnClass) || attrs.lnClass || "", ""],
      ]);

    if (lntDef && lntDef.dos && lntDef.dos.length) {
      html += '<div class="detail-section">';
      html +=
        '<div class="detail-section-title">Data Objects (' +
        lntDef.dos.length +
        ") — desde DataTypeTemplates</div>";
      lntDef.dos.forEach(function (doEntry) {
        var doTypeDef = doTypeUtils && doTypeUtils.getDoTypeDefinition
          ? doTypeUtils.getDoTypeDefinition(doTypeIndex, doEntry.type)
          : (doTypeIndex[doEntry.type] || null);
        var cdc = doTypeDef ? doTypeDef.cdc : "";
        html += doCard(doEntry, doTypeDef, cdc, {
          lnType: lnTypeId,
          attrs: attrs,
          ctx: meta.ctx || {},
        });
      });
      html += "</div>";
    }
  } else if (tag === "DO_SYNTH") {
    var de = meta.doEntry || {};
    var doCtx = meta.ctx || {};
    var doTypeId = de.type || attrs.type || attrs.DOType || "";
    var dtd = meta.doTypeDef || (doTypeId ? getDoTypeDef(doTypeId) : null);
    var cdc = dtd ? dtd.cdc : (attrs.CDC || attrs.cdc || "");
    var cidAttrs = [];
    var lnTypeId = attrs.lnType || de.lnType || doCtx.lnType || "";
    var ldInstValue = attrs.ldInst || doCtx.ldInst || "";
    var prefixValue = attrs.prefix || doCtx.prefix || "";
    var lnClassValue = attrs.lnClass || doCtx.lnClass || (lnTypeId && lnodeTypeIndex[lnTypeId] ? lnodeTypeIndex[lnTypeId].lnClass || "" : "");
    var lnInstValue = attrs.lnInst || doCtx.lnInst || "";
    var doNameValue = de.name || attrs.name || doCtx.doName || "";
    if (ldInstValue) cidAttrs.push(["ldInst", ldInstValue, ""]);
    if (prefixValue) cidAttrs.push(["prefix", prefixValue, ""]);
    if (lnClassValue) cidAttrs.push(["lnClass", lnClassValue, ""]);
    if (lnInstValue) cidAttrs.push(["lnInst", lnInstValue, ""]);
    if (lnTypeId) cidAttrs.push(["LNodeType", lnTypeId, "blue"]);
    if (meta.ctx && meta.ctx.ldDesc) cidAttrs.push(["LD Desc (Logical Device Description)", meta.ctx.ldDesc, ""]);
    if (doNameValue) cidAttrs.push(["doName", doNameValue, "highlight"]);
    if (doTypeId) cidAttrs.push(["type", doTypeId, "blue"]);

    if (cidAttrs.length) {
      html += section("Atributos del Nodo", cidAttrs);
    }

    if (dtd) {
      html += '<div class="detail-section">';
      html +=
        '<div class="detail-section-title">Data Attributes (' +
        dtd.das.length +
        ")</div>";
      html += daTable(dtd.das);
      html += "</div>";
    }
  } else if (tag === "DO_TYPE_CONTENT") {
    var doCtx = meta.ctx || {};
    var cidAttrs = [];
    if (attrs.ldInst || doCtx.ldInst) cidAttrs.push(["ldInst", attrs.ldInst || doCtx.ldInst || "", ""]);
    if (attrs.prefix || doCtx.prefix) cidAttrs.push(["prefix", attrs.prefix || doCtx.prefix || "", ""]);
    if (attrs.lnClass || doCtx.lnClass) cidAttrs.push(["lnClass", attrs.lnClass || doCtx.lnClass || "", ""]);
    if (attrs.lnInst || doCtx.lnInst) cidAttrs.push(["lnInst", attrs.lnInst || doCtx.lnInst || "", ""]);
    if (attrs.lnType || doCtx.lnType) cidAttrs.push(["LNodeType", attrs.lnType || doCtx.lnType || "", "blue"]);
    if (meta.ctx && meta.ctx.ldDesc) cidAttrs.push(["LD Desc (Logical Device Description)", meta.ctx.ldDesc, ""]);
    if (attrs.doName || doCtx.doName) cidAttrs.push(["doName", attrs.doName || doCtx.doName || "", "highlight"]);
    if (cidAttrs.length) {
      html += section("Atributos del Nodo", cidAttrs);
    }
    html += section("DOType Contenido", [
      ["id", attrs.id || "", "blue"],
      ["CDC", attrs.CDC || attrs.cdc || "", "pink"],
    ]);
    var doTypeId = attrs.id || "";
    if (doTypeId && doTypeIndex[doTypeId]) {
      var doTypeDef = doTypeIndex[doTypeId];
      if (doTypeDef.das && doTypeDef.das.length) {
        html += '<div class="detail-section">';
        html += '<div class="detail-section-title">Data Attributes (' + doTypeDef.das.length + ')</div>';
        html += daTable(doTypeDef.das);
        html += '</div>';
      }
    }
  } else if (tag === "DA_TYPE_CONTENT") {
    var dataTypeCtx = meta.ctx || {};
    var dataTypeId = attrs.type || attrs.id || "";
    var dataTypeDef = dataTypeId && daTypeIndex[dataTypeId] ? daTypeIndex[dataTypeId] : null;
    var cidAttrs = [];
    if (attrs.ldInst || dataTypeCtx.ldInst) cidAttrs.push(["ldInst", attrs.ldInst || dataTypeCtx.ldInst || "", ""]);
    if (attrs.prefix || dataTypeCtx.prefix) cidAttrs.push(["prefix", attrs.prefix || dataTypeCtx.prefix || "", ""]);
    if (attrs.lnClass || dataTypeCtx.lnClass) cidAttrs.push(["lnClass", attrs.lnClass || dataTypeCtx.lnClass || "", ""]);
    if (attrs.lnInst || dataTypeCtx.lnInst) cidAttrs.push(["lnInst", attrs.lnInst || dataTypeCtx.lnInst || "", ""]);
    if (attrs.lnType || dataTypeCtx.lnType) cidAttrs.push(["LNodeType", attrs.lnType || dataTypeCtx.lnType || "", "blue"]);
    if (attrs.doName || dataTypeCtx.doName) cidAttrs.push(["doName", attrs.doName || dataTypeCtx.doName || "", "highlight"]);
    if (attrs.name || dataTypeCtx.daName) cidAttrs.push(["daName", attrs.name || dataTypeCtx.daName || "", ""]);
    if (meta.ctx && meta.ctx.ldDesc) cidAttrs.push(["LD Desc (Logical Device Description)", meta.ctx.ldDesc, ""]);
    if (cidAttrs.length) {
      html += section("Atributos del Nodo", cidAttrs);
    }

    html += section("Datatype", [
      ["id", dataTypeId, "blue"],
      ["Elementos BDA", dataTypeDef && dataTypeDef.bdas ? String(dataTypeDef.bdas.length) + " BDA(s)" : "", ""],
    ]);

    if (dataTypeDef && dataTypeDef.bdas && dataTypeDef.bdas.length) {
      html += '<div class="detail-section">';
      html += '<div class="detail-section-title">Contenido Datatype (' + dataTypeDef.bdas.length + ')</div>';
      html += renderBdaTreeRows(dataTypeDef.bdas, 0);
      html += '</div>';
    } else {
      html += '<div class="empty-msg">Este Datatype no tiene BDA definidos.</div>';
    }
  } else if (tag === "DA_SYNTH") {
    var daCtx = meta.ctx || {};
    var daTypeIndexEntry = attrs.type && daTypeIndex[attrs.type] ? daTypeIndex[attrs.type] : null;
    var cidAttrs = [];
    if (attrs.ldInst || daCtx.ldInst) cidAttrs.push(["ldInst", attrs.ldInst || daCtx.ldInst || "", ""]);
    if (attrs.prefix || daCtx.prefix) cidAttrs.push(["prefix", attrs.prefix || daCtx.prefix || "", ""]);
    if (attrs.lnClass || daCtx.lnClass) cidAttrs.push(["lnClass", attrs.lnClass || daCtx.lnClass || "", ""]);
    if (attrs.lnInst || daCtx.lnInst) cidAttrs.push(["lnInst", attrs.lnInst || daCtx.lnInst || "", ""]);
    if (attrs.lnType || daCtx.lnType) cidAttrs.push(["LNodeType", attrs.lnType || daCtx.lnType || "", "blue"]);
    if (meta.ctx && meta.ctx.ldDesc) cidAttrs.push(["LD Desc (Logical Device Description)", meta.ctx.ldDesc, ""]);
    if (attrs.doName || daCtx.doName) cidAttrs.push(["doName", attrs.doName || daCtx.doName || "", ""]);
    if (cidAttrs.length) {
      html += section("Atributos del Nodo", cidAttrs);
    }
    html +=
      section("Data Attribute", Object.keys(attrs).map(function (key) {
        return [key, attrs[key] || "", key === "name" ? "highlight" : (key === "fc" ? "blue" : "")];
      }));

    if (daTypeIndexEntry && daTypeIndexEntry.bdas && daTypeIndexEntry.bdas.length) {
      html += '<div class="detail-section">';
      html += '<div class="detail-section-title">BDA del Datatype</div>';
      html += renderBdaTreeRows(daTypeIndexEntry.bdas, 0);
      html += '</div>';
    }

    if (attrs.type) {
      html += extraSection("Detalles adicionales", [
        ["DAType", attrs.type || "", "blue"],
        ["bType", attrs.bType || attrs.DAbType || "", ""],
        ["fc", attrs.fc || "", "blue"],
        ["CDC", attrs.CDC || attrs.cdc || "", "pink"],
      ]);
    }
  } else if (tag === "BDA_SYNTH" || tag === "BDA" || tag === "BDA_CONTENT") {
    var bdaAttrs = meta.attrs || {};
    var bdaRows = filterNonEmptyRows([
      ["name", bdaAttrs.name || "", "highlight"],
      ["fc", bdaAttrs.fc || "", "blue"],
      ["bType", bdaAttrs.bType || "", ""],
      ["type", bdaAttrs.type || "", "blue"],
    ]);
    if (bdaRows.length) {
      html += section("BDA", bdaRows);
    }
    var bdaTypeEntry = bdaAttrs.type && daTypeIndex[bdaAttrs.type] ? daTypeIndex[bdaAttrs.type] : null;
    if ((tag === "BDA_SYNTH" || tag === "BDA") && bdaTypeEntry && bdaTypeEntry.bdas && bdaTypeEntry.bdas.length) {
      html += '<div class="detail-section">';
      html += '<div class="detail-section-title">Contenido BDA (' + bdaTypeEntry.bdas.length + ")</div>";
      html += renderBdaTreeRows(bdaTypeEntry.bdas, 0);
      html += '</div>';
    }
    if (tag === "BDA_CONTENT" && bdaTypeEntry && bdaTypeEntry.bdas && bdaTypeEntry.bdas.length) {
      html += '<div class="detail-section">';
      html += '<div class="detail-section-title">Contenido BDA (' + bdaTypeEntry.bdas.length + ")</div>";
      bdaTypeEntry.bdas.forEach(function (nestedBda) {
        html += '<div class="da-row" style="border-bottom:1px solid #1e293b;padding:8px 0">';
        html += '<span class="da-name" style="color:#93c5fd">' + esc(nestedBda.name || "") + "</span>";
        html += '<span class="da-fc">' + esc(nestedBda.fc || "") + "</span>";
        html += '<span class="da-btype">' + esc(nestedBda.bType || "") + "</span>";
        html += '<span class="da-type">' + esc(nestedBda.type || "") + "</span>";
        html += "</div>";
      });
      html += "</div>";
    }
  } else if (tag === "EnumVal") {
    html +=
      '<div style="padding:16px;background:#111827;border:1px solid #334155;border-radius:12px;max-width:100%;margin-bottom:16px">';
    html +=
      '<div style="font-size:14px;color:#60a5fa;font-weight:700;margin-bottom:8px">Enum Value</div>';
    html +=
      '<div style="display:grid;grid-template-columns:1fr 1fr;gap:10px;margin-bottom:14px">';
    html +=
      '<div style="background:#0f172a;padding:12px;border:1px solid #1e293b;border-radius:10px">';
    html += '<div style="font-size:12px;color:#94a3b8;margin-bottom:4px">Orden</div>';
    html += '<div style="font-size:16px;font-weight:700;color:#e2e8f0">' + esc(attrs.ord || "") + '</div>';
    html += '</div>';
    html +=
      '<div style="background:#0f172a;padding:12px;border:1px solid #1e293b;border-radius:10px">';
    html += '<div style="font-size:12px;color:#94a3b8;margin-bottom:4px">Tipo</div>';
    html += '<div style="font-size:16px;font-weight:700;color:#60a5fa">' + esc(attrs.type || "") + '</div>';
    html += '</div>';
    html += '</div>';
    html +=
      '<div style="padding:12px;background:#0f172a;border:1px solid #1e293b;border-radius:10px">';
    html += '<div style="font-size:12px;color:#94a3b8;margin-bottom:4px">Valor</div>';
    html += '<div style="font-size:15px;font-weight:600;color:#d1d5db">' + esc(attrs.text || "") + '</div>';
    html += '</div>';
    html += '</div>';

    if (attrs.type) {
      // EnumType values are shown in the dedicated EnumType panel
    }
  } else if (tag === "FCDA" || tag === "FCDA_GROUP") {
    var fcdaRows = filterNonEmptyRows([
      ["ldInst", attrs.ldInst || "", ""],
      ["prefix", attrs.prefix || "", ""],
      ["lnClass", attrs.lnClass || "", ""],
      ["lnInst", attrs.lnInst || "", ""],
      ["LNodeType", attrs.lnType || "", "blue"],
      ["LD Desc (Logical Device Description)", (meta.ctx && meta.ctx.ldDesc) || attrs.ldDesc || "", ""],
      ["doName", attrs.doName || "", "highlight"],
      ["daName", attrs.daName || "", ""],
      ["fc", attrs.fc || "", "blue"],
    ]);
    if (fcdaRows.length) {
      html += section("FCDA", fcdaRows);
    }
  } else {
    html += section("Atributos del Nodo", Object.keys(attrs).map(function (key) {
      return [key, attrs[key] || "", ""];
    }));
  }

  c.innerHTML = html;
}

function buildTreeNode(xmlNode, depth, context) {
  if (!xmlNode || (!hasAttrs(xmlNode) && !hasTextValue(xmlNode))) return null;

  var tag = localName(xmlNode);
  if (tag === "EnumVal") return null;
  var textValue = getTextValue(xmlNode);
  var geta = function (name) {
    return xmlNode.getAttribute ? xmlNode.getAttribute(name) || "" : "";
  };
  var label = tag;
  if (tag === "DataTypeTemplates") label = "Datatype Templates";
  if (tag === "EnumType" && geta("id")) label += ": " + geta("id");
  else if (tag === "DOType" && geta("id")) label = "Datatype";
  else if (tag === "DAType" && geta("id")) label = "Datatype";
  else if (tag === "DA" && geta("name")) {
    label = "DA " + geta("name") + (geta("fc") ? " · fc=" + geta("fc") : "") + (geta("bType") ? " · " + geta("bType") : "");
  }
  else if (tag === "BDA" && geta("name")) {
    label = "BDA " + geta("name") + (geta("fc") ? " · fc=" + geta("fc") : "") + (geta("bType") ? " · " + geta("bType") : "");
  }
  else if (tag === "FCDA") {
    var daName = geta("daName") || "";
    var doName = geta("doName") || "";
    label = "FCDA " + doName + " · " + daName;
  }
  else if (tag === "LN" || tag === "LN0") {
    var prefix = geta("prefix") || "";
    var lnClass = geta("lnClass") || "";
    var inst = geta("inst") || "";
    var lnId = [prefix, lnClass, inst].filter(function (v) { return v; }).join("");
    label = (tag === "LN0" ? "LN0" : "LN") + " " + lnId;
    if (!lnId) label = (tag === "LN0" ? "LN0" : "LN");
  }
  else if (tag === "Val" && textValue) label += ": " + textValue;
  else if (geta("name")) label += ": " + geta("name");
  else if (geta("inst")) label += ": " + geta("inst");
  else if (geta("lnClass")) label += ": " + geta("lnClass");

  var attrs = {};
  if (xmlNode.attributes)
    for (var i = 0; i < xmlNode.attributes.length; i++) {
      attrs[xmlNode.attributes[i].name] = xmlNode.attributes[i].value;
    }

  if (textValue) {
    attrs.value = textValue;
    attrs.text = textValue;
    attrs["Val"] = textValue;
  }

  var ctx = Object.assign({}, context || {});
  if (tag === "IED") ctx.iedName = geta("name");
  if (tag === "LDevice") {
    ctx.lDeviceInst = geta("inst") || "";
    if (!ctx.ldInst) ctx.ldInst = ctx.lDeviceInst;
    ctx.ldDesc = (ctx.lDeviceInst && ldDescByLdInst[ctx.lDeviceInst])
      ? ldDescByLdInst[ctx.lDeviceInst]
      : (geta("desc") || "");
  }
  if (tag === "DataSet") {
    ctx.dataSet = geta("name");
    ctx.dataSetDesc = geta("desc") || "";
  }
  if (tag === "LN" || tag === "LN0") {
    ctx.prefix = geta("prefix");
    ctx.lnClass = geta("lnClass");
    ctx.lnInst = geta("inst");
    ctx.lnDesc = geta("desc") || "";
    ctx.desc = ctx.lnDesc;
    ctx.lnType = geta("lnType");
    if (!ctx.ldInst) ctx.ldInst = ctx.lDeviceInst || "";
    if (!attrs.ldInst && ctx.ldInst) attrs.ldInst = ctx.ldInst;
  }

  var meta = {
    tag: tag,
    attrs: attrs,
    ctx: Object.assign({}, ctx),
  };

  var children = [];

  if (tag === "DataTypeTemplates") {
    children = children.concat(buildDataTypeTemplatesTreeChildren(ctx));
  }

  if (tag === "DOType" && geta("id") && doTypeIndex[geta("id")]) {
    children.push(buildDoTypeContenidoNode(geta("id"), ctx, "contenido"));
  }

  if (tag === "DAType" && geta("id") && daTypeIndex[geta("id")]) {
    var daTypeDef = daTypeIndex[geta("id")];
    var bdaBranchChildren = [];
    if (enumTypeIndex[geta("id")] && enumTypeIndex[geta("id")].vals && enumTypeIndex[geta("id")].vals.length) {
      children.push({
        text: "EnumType " + geta("id"),
        icon: "fa fa-list-alt",
        children: enumTypeIndex[geta("id")].vals.map(function (val) {
          return {
            text: (val.ord ? val.ord + " - " : "") + (val.text || ""),
            icon: "fa fa-circle",
            children: [],
            a_attr: { title: val.text || "" },
            attributes: { tag: "EnumVal", attrs: { ord: val.ord || "", type: geta("id"), text: val.text || "" } },
            _meta: { tag: "EnumVal", attrs: { ord: val.ord || "", type: geta("id"), text: val.text || "" } },
          };
        }),
        state: { opened: false },
        a_attr: { title: "EnumType: " + geta("id") },
        attributes: { tag: "EnumType", attrs: { id: geta("id") } },
        _meta: { tag: "EnumType", attrs: { id: geta("id") } },
      });
    }
    (daTypeDef.bdas || []).forEach(function (bda) {
      var bdaLabel = "BDA " + (bda.name || "") + (bda.fc ? " · fc=" + bda.fc : "") + (bda.bType ? " · " + bda.bType : "");
      bdaBranchChildren.push({
        text: bdaLabel,
        icon: "fa fa-circle",
        children: buildBdaTreeChildren(bda, ctx),
        state: { opened: false },
        a_attr: { title: bdaLabel },
        attributes: { tag: "BDA_SYNTH", attrs: Object.assign({ name: bda.name, fc: bda.fc, bType: bda.bType, type: bda.type }, bda.attrs || {}) },
        _meta: { tag: "BDA_SYNTH", attrs: Object.assign({ name: bda.name, fc: bda.fc, bType: bda.bType, type: bda.type }, bda.attrs || {}) },
      });
    });
    children.push({
      text: "Contenido Datatype",
      icon: "fa fa-sitemap",
      children: bdaBranchChildren,
      state: { opened: false },
      a_attr: { title: "Contenido Datatype" },
      attributes: { tag: "DA_TYPE_CONTENT", attrs: { id: geta("id") } },
      _meta: { tag: "DA_TYPE_CONTENT", attrs: { id: geta("id") }, ctx: Object.assign({}, ctx || {}) },
    });
  }

  if ((tag === "LN" || tag === "LN0") && attrs.lnType) {
    var lnt = lnodeTypeIndex[attrs.lnType];
    if (lnt) {
      attrs["lnType (CID)"] = attrs.lnType;
      attrs["lnClass (CID)"] = lnt.lnClass || attrs.lnClass || "";
      meta.attrs = attrs;
      meta.ctx = Object.assign({}, ctx);

      var groupedByType = {};
      lnt.dos.forEach(function (doEntry) {
        var doTypeDef = doTypeUtils && doTypeUtils.getDoTypeDefinition
          ? doTypeUtils.getDoTypeDefinition(doTypeIndex, doEntry.type)
          : (doTypeIndex[doEntry.type] || null);
        var cdc = doTypeDef ? doTypeDef.cdc : "";
        var key = doEntry.type || "(sin tipo)";
        if (!groupedByType[key]) {
          groupedByType[key] = { doTypeDef: doTypeDef, cdc: cdc, entries: [] };
        }
        groupedByType[key].entries.push({ doEntry: doEntry, doTypeDef: doTypeDef, cdc: cdc });
      });

      Object.keys(groupedByType).forEach(function (typeKey) {
        var group = groupedByType[typeKey];
        var hasDoInfo = group.entries.some(function (entry) {
          return entry.doTypeDef && (entry.doTypeDef.das && entry.doTypeDef.das.length > 0 || entry.doTypeDef.sdos && entry.doTypeDef.sdos.length > 0);
        });
        if (!hasDoInfo) return;

        var isStruct = String(group.cdc || "").toLowerCase().indexOf("struct") !== -1;
        var groupChildren = [];
        var typeLabel = group.cdc ? group.cdc : typeKey;

        group.entries.forEach(function (entry) {
          var doEntry = entry.doEntry;
          var doTypeDef = entry.doTypeDef;
          var cdc = entry.cdc;
          var doSummary = doEntry.name + (doEntry.type ? " | ID: " + doEntry.type : "") + (cdc ? " | CDC: " + cdc : "");
          var doTypeLabel = doEntry.type ? " [ID: " + doEntry.type + "]" : "";
          var doCdcLabel = cdc ? " [CDC: " + cdc + "]" : "";
          var daSummary = doTypeDef && doTypeDef.das ? doTypeDef.das.map(function (da) {
            var parts = [da.name];
            if (da.fc) parts.push("fc=" + da.fc);
            if (da.bType) parts.push("bType=" + da.bType);
            if (da.type) parts.push("type=" + da.type);
            return parts.join(" | ");
          }).join(", ") : "";
          var doMeta = {
            tag: "DO_SYNTH",
            attrs: { name: doEntry.name, type: doEntry.type, CDC: cdc },
            doEntry: doEntry,
            doTypeDef: doTypeDef,
            ctx: Object.assign({}, ctx),
          };

          if (isStruct && doTypeDef && doTypeDef.das && doTypeDef.das.length) {
            var daNodes = [];
            if (doTypeDef) {
              doTypeDef.das.forEach(function (da) {
                var daLabel = "DA " + da.name + (da.fc ? " · fc=" + da.fc : "") + (da.bType ? " · " + da.bType : "");
                var daMeta = {
                  tag: "DA_SYNTH",
                  attrs: Object.assign({ name: da.name, fc: da.fc, bType: da.bType, type: da.type }, da.attrs || {}),
                  da: da,
                  ctx: Object.assign({}, ctx),
                };
                var daChildren = [];
                if (isStructDaEntry(da) && da.type && daTypeIndex[da.type]) {
                  daTypeIndex[da.type].bdas.forEach(function (bda) {
                    var bdaLabel = "BDA " + bda.name + (bda.fc ? " · fc=" + bda.fc : "") + (bda.bType ? " · " + bda.bType : "");
                    var bdaChildren = buildBdaTreeChildren(bda, ctx);
                    daChildren.push({
                      text: bdaLabel,
                      icon: "fa fa-circle",
                      children: bdaChildren,
                      state: { opened: bdaChildren.length > 0 || isStructBdaEntry(bda) },
                      a_attr: { title: bdaLabel },
                      attributes: {
                        tag: "BDA_SYNTH",
                        attrs: Object.assign({ name: bda.name, fc: bda.fc, bType: bda.bType, type: bda.type }, bda.attrs || {}),
                      },
                      _meta: {
                        tag: "BDA_SYNTH",
                        attrs: Object.assign({ name: bda.name, fc: bda.fc, bType: bda.bType, type: bda.type }, bda.attrs || {}),
                        ctx: Object.assign({}, ctx),
                      },
                    });
                  });
                }
                daNodes.push({
                  text: daLabel,
                  icon: "fa fa-tag",
                  children: daChildren,
                  state: { opened: daChildren.length > 0 || isStructDaEntry(da) },
                  a_attr: { title: daLabel },
                  attributes: daMeta,
                  _meta: daMeta,
                });
              });
              if (doTypeDef.sdos && doTypeDef.sdos.length) {
                var sdoBranchCtx = Object.assign({}, ctx, {
                  doName: doEntry.name || "",
                  lnType: attrs.lnType || ctx.lnType || "",
                });
                doTypeDef.sdos.forEach(function (sdo) {
                  daNodes.push(buildSdoContenidoNode(sdo, sdoBranchCtx));
                });
              }
            }
            groupChildren.push({
              text: appendBehSuffix("DO " + doEntry.name, doEntry.name),
              icon: "fa fa-database",
              children: daNodes,
              state: { opened: false },
              a_attr: { title: doSummary },
              attributes: doMeta,
              _meta: doMeta,
            });
          } else {
            groupChildren.push({
              text: appendBehSuffix("DO " + doEntry.name, doEntry.name),
              icon: "fa fa-database",
              children: [],
              state: { opened: false },
              a_attr: { title: doSummary },
              attributes: doMeta,
              _meta: doMeta,
            });
          }
        });

        children.push({
          text: typeLabel,
          icon: isStruct ? "fa fa-sitemap" : "fa fa-cube",
          children: groupChildren,
          state: { opened: false },
          a_attr: { title: typeKey + (group.cdc ? " [" + group.cdc + "]" : "") },
          attributes: {
            tag: "DO_TYPE_GROUP",
            attrs: { type: typeKey, CDC: group.cdc },
          },
          _meta: {
            tag: "DO_TYPE_GROUP",
            attrs: { type: typeKey, CDC: group.cdc },
          },
        });
      });
    }
  }

  for (var j = 0; j < xmlNode.children.length; j++) {
    var childXml = xmlNode.children[j];
    var childTag = localName(childXml);
    if (
      tag === "DataTypeTemplates" &&
      (childTag === "LNodeType" || childTag === "DOType" || childTag === "DAType" || childTag === "EnumType")
    ) {
      continue;
    }
    var childNode = buildTreeNode(childXml, depth + 1, ctx);
    if (childNode) children.push(childNode);
  }

  if (tag === "FCDA") {
    var resolvedLdInst = geta("ldInst") || attrs.ldInst || getEffectiveLdInst(ctx, attrs) || "";
    var resolvedPrefix = geta("prefix") || attrs.prefix || ctx.prefix || "";
    var resolvedLnClass = geta("lnClass") || attrs.lnClass || ctx.lnClass || "";
    var resolvedLnInst = geta("lnInst") || attrs.lnInst || ctx.lnInst || "";
    var resolvedLnType = geta("lnType") || attrs.lnType || ctx.lnType || "";
    var fCtx = {
      iedName: ctx.iedName || "",
      dataSet: ctx.dataSet || "",
      ldInst: resolvedLdInst,
      prefix: resolvedPrefix,
      lnClass: resolvedLnClass,
      lnInst: resolvedLnInst,
      doName: geta("doName"),
    };
    var prefix = resolvedPrefix;
    var lnClass = resolvedLnClass;
    var lnInst = resolvedLnInst;
    var doName = geta("doName") || "";
    var daName = geta("daName") || "";
    var lnTypeName = resolvedLnType;
    var doTypeName = "";
    var cdc = "";
    var daType = "";
    var daBType = "";
    if (lnTypeName && doName && lnodeTypeIndex[lnTypeName]) {
      var match = findNamedEntry(lnodeTypeIndex[lnTypeName].dos, doName) || lnodeTypeIndex[lnTypeName].dos.find(function (entry) {
        return entry.name === doName;
      });
      if (match) {
        doTypeName = match.type || "";
        var doTypeDef = doTypeUtils && doTypeUtils.getDoTypeDefinition
          ? doTypeUtils.getDoTypeDefinition(doTypeIndex, doTypeName)
          : (doTypeIndex[doTypeName] || null);
        if (doTypeDef) {
          cdc = doTypeDef.cdc || "";
          if (daName && doTypeDef.das && doTypeDef.das.length) {
            var daDef = findNamedEntry(doTypeDef.das, daName) || doTypeDef.das.find(function (d) {
              return d.name === daName;
            });
            if (daDef) {
              daType = daDef.type || "";
              daBType = daDef.bType || "";
            }
          }
        }
      }
    }
    var desc = buildCompositeDescription(
      ctx.ldDesc || "",
      ctx.lnDesc || ctx.desc || "",
      getDoiDescriptionForContext(doName, fCtx, attrs, ctx)
    );
    var ldDescValue = ctx.ldDesc || "";
    var lnDescValue = ctx.lnDesc || ctx.desc || "";
    var doDescValue = getDoiDescriptionForContext(doName, fCtx, attrs, ctx);
    attrs.doName = doName || attrs.doName || "";
    attrs.daName = daName || attrs.daName || "";
    attrs.fc = geta("fc") || attrs.fc || "";
    if (tag === "FCDA") {
      attrs.ldInst = resolvedLdInst;
      attrs.prefix = resolvedPrefix;
      attrs.lnClass = resolvedLnClass;
      attrs.lnInst = resolvedLnInst;
      attrs.lnType = resolvedLnType;
    } else {
      attrs.ldInst = geta("ldInst") || attrs.ldInst || "";
      attrs.prefix = prefix || attrs.prefix || ctx.prefix || "";
      attrs.lnClass = lnClass || attrs.lnClass || ctx.lnClass || "";
      attrs.lnInst = lnInst || attrs.lnInst || ctx.lnInst || "";
    }
    ctx.ldInst = attrs.ldInst;
    ctx.prefix = attrs.prefix;
    ctx.lnClass = attrs.lnClass;
    ctx.lnInst = attrs.lnInst;
    ctx.lnType = attrs.lnType || ctx.lnType;
    attrs.DAType = daType || attrs.DAType || "";
    attrs.DAbType = daBType || attrs.DAbType || "";
    attrs.CDC = cdc || attrs.CDC || attrs.cdc || "";
    attrs.DOType = doTypeName || attrs.DOType || "";
    var lnIdentifier = prefix + lnClass + lnInst;
    var lnTypeDef = lnodeTypeIndex[lnTypeName] || null;
    var cidLnClass = lnTypeDef ? (lnTypeDef.lnClass || "") : "";
    var dosDefinidos = lnTypeDef ? (lnTypeDef.dos.length + " DO(s) en DataTypeTemplates") : "";
    var concatValue = [resolvedLdInst, prefix + lnClass + lnInst, doName, daName]
      .filter(function (value) {
        return value;
      })
      .join(".");
    lnRecords.push({
      IED: ctx.iedName || "",
      DataSet: ctx.dataSet || "",
      LDInst: resolvedLdInst,
      Prefix: prefix,
      LNClass: lnClass,
      LNInst: lnInst,
      LNodeType: lnTypeName,
      lnClassCID: cidLnClass,
      DOsDefinidos: dosDefinidos,
      DOName: doName,
      DOType: doTypeName,
      CDC: cdc,
      DAName: daName,
      DAType: daType,
      DAbType: daBType,
      Description: desc,
      LDDesc: ldDescValue,
      LNDesc: lnDescValue,
      DODesc: doDescValue,
      fc: geta("fc"),
      Tag: "FCDA",
      IECRef: buildRef(fCtx),
      CONCAT: concatValue,
      _searchText: buildDatasetSearchText({
        IED: ctx.iedName || "",
        DataSet: ctx.dataSet || "",
        LDInst: resolvedLdInst,
        Prefix: prefix,
        LNClass: lnClass,
        LNInst: lnInst,
        LNodeType: lnTypeName,
        lnClassCID: cidLnClass,
        DOsDefinidos: dosDefinidos,
        DOName: doName,
        DOType: doTypeName,
        CDC: cdc,
        DAName: daName,
        fc: geta("fc"),
        Tag: "FCDA",
        CONCAT: concatValue,
      }),
    });
    meta.attrs = attrs;
    meta.ctx = Object.assign({}, ctx);
  }

  var icon = "fa fa-cube";
  if (tag === "IED") icon = "fa fa-server";
  else if (tag === "LDevice") icon = "fa fa-hdd";
  else if (tag === "LN" || tag === "LN0") icon = "fa fa-layer-group";
  else if (tag === "DataSet") icon = "fa fa-database";
  else if (tag === "DataTypeTemplates" || tag === "LNTYPE_GROUP" || tag === "DOTYPE_GROUP" || tag === "ENUMTYPE_GROUP") icon = "fa fa-sitemap";
  else if (tag === "EnumType") icon = "fa fa-list-alt";
  else if (tag === "EnumVal") icon = "fa fa-circle";
  else if (tag === "FCDA") icon = "fa fa-link";
  else if (tag === "ReportControl") icon = "fa fa-bell";
  else if (tag === "GSEControl") icon = "fa fa-broadcast-tower";
  else if (tag === "SampledValueControl") icon = "fa fa-wave-square";

  var treeNode = {
    text: label,
    icon: icon,
    children: children,
    attributes: meta,
    _meta: meta,
    a_attr: {
      title: label + (attrs.name ? " — " + attrs.name : "")
    },
  };
  flatNodes.push({
    text: label,
    attrs: attrs,
    depth: depth,
    rawName: attrs.name || label,
    rawTag: tag,
  });
  return treeNode;
}

function isStructBType(bType) {
  return String(bType || "").toLowerCase() === "struct";
}

function isEnumBType(bType) {
  return String(bType || "").toLowerCase() === "enum";
}

function isStructBdaEntry(bda) {
  if (!bda) return false;
  return isStructBType(bda.bType);
}

function isStructDaEntry(da) {
  if (!da) return false;
  return isStructBType(da.bType);
}

function getDoTypeDef(doTypeId) {
  if (!doTypeId) return null;
  return doTypeUtils && doTypeUtils.getDoTypeDefinition
    ? doTypeUtils.getDoTypeDefinition(doTypeIndex, doTypeId)
    : (doTypeIndex[doTypeId] || null);
}

function getDaTypeDef(daTypeId) {
  if (!daTypeId) return null;
  return daTypeIndex[daTypeId] || null;
}

function buildDoTypeDaBranchChildren(doTypeDef, ctx) {
  var daChildren = [];
  
  if (doTypeDef && doTypeDef.das && doTypeDef.das.length) {
    doTypeDef.das.forEach(function (da) {
      var daLabel = "DA " + (da.name || "") + (da.fc ? " · fc=" + da.fc : "") + (da.bType ? " · " + da.bType : "");
      var daTypeChildren = [];
      if (da.type && isStructDaEntry(da)) {
        var daTypeLabel = "Datatype";
        var daTypeBranch = {
          text: daTypeLabel,
          icon: "fa fa-tags",
          children: [],
          state: { opened: false },
          a_attr: { title: daTypeLabel },
          attributes: { tag: "DAType", attrs: { id: da.type } },
          _meta: { tag: "DAType", attrs: { id: da.type } },
        };
        if (daTypeIndex[da.type] && daTypeIndex[da.type].bdas && daTypeIndex[da.type].bdas.length) {
          daTypeBranch.children.push({
            text: "Contenido Datatype",
            icon: "fa fa-sitemap",
            children: buildDaTypeChildren(da, ctx),
            state: { opened: false },
            a_attr: { title: "Contenido Datatype" },
            attributes: { tag: "DA_TYPE_CONTENT", attrs: { id: da.type } },
            _meta: { tag: "DA_TYPE_CONTENT", attrs: { id: da.type } },
          });
        }
        daTypeChildren.push(daTypeBranch);
      }
      var daAttrs = Object.assign({ name: da.name, fc: da.fc, bType: da.bType, type: da.type }, da.attrs || {});
      if (ctx) {
        if (ctx.ldInst) daAttrs.ldInst = ctx.ldInst;
        if (ctx.prefix) daAttrs.prefix = ctx.prefix;
        if (ctx.lnClass) daAttrs.lnClass = ctx.lnClass;
        if (ctx.lnInst) daAttrs.lnInst = ctx.lnInst;
        if (ctx.lnType) daAttrs.lnType = ctx.lnType;
        if (ctx.doName) daAttrs.doName = ctx.doName;
        if (ctx.sdoName) daAttrs.sdoName = ctx.sdoName;
      }
      daChildren.push({
        text: daLabel,
        icon: "fa fa-tag",
        children: daTypeChildren,
        state: { opened: daTypeChildren.length > 0 || isStructDaEntry(da) },
        a_attr: { title: daLabel },
        attributes: { tag: "DA_SYNTH", attrs: daAttrs },
        _meta: { tag: "DA_SYNTH", attrs: daAttrs },
      });
    });
  }

  if (doTypeDef && doTypeDef.sdos && doTypeDef.sdos.length) {
    doTypeDef.sdos.forEach(function (sdo) {
      daChildren.push(buildSdoContenidoNode(sdo, ctx));
    });
  }

  return daChildren;
}

function buildSdoContenidoNode(sdo, ctx) {
  var sdoName = sdo && sdo.name ? sdo.name : "";
  var sdoTypeId = sdo && sdo.type ? sdo.type : "";
  var trail = ctx && Array.isArray(ctx.__doTypeTrail) ? ctx.__doTypeTrail.slice() : [];
  var children = [];

  if (sdoTypeId && trail.indexOf(sdoTypeId) === -1) {
    var nextCtx = Object.assign({}, ctx || {}, {
      sdoName: sdoName,
      __doTypeTrail: trail.concat([sdoTypeId]),
    });
    children = [buildDoTypeContenidoNode(sdoTypeId, nextCtx, "Contenido", false)];
  }

  return {
    text: "SDO: " + sdoName,
    icon: "fa fa-share-alt",
    children: children,
    state: { opened: children.length > 0 },
    a_attr: { title: "SDO: " + sdoName },
    attributes: { tag: "SDO_SYNTH", attrs: { name: sdoName, type: sdoTypeId, doName: ctx && ctx.doName ? ctx.doName : "", sdoName: sdoName } },
    _meta: {
      tag: "SDO_SYNTH",
      attrs: { name: sdoName, type: sdoTypeId, doName: ctx && ctx.doName ? ctx.doName : "", sdoName: sdoName },
      ctx: Object.assign({}, ctx || {}, { sdoName: sdoName }),
    },
  };
}

function buildDoFcdaBranchChildren(lnTypeId, doName, ctx) {
  var children = [];
  if (!lnTypeId || !doName || !Array.isArray(lnRecords) || !lnRecords.length) return children;
  var targetLdInst = getEffectiveLdInst(ctx);

  var records = lnRecords.filter(function (rec) {
    if (!rec) return false;
    if (normalizeName(rec.DOName || "") !== normalizeName(doName)) return false;
    if (lnTypeId && rec.LNodeType && normalizeName(rec.LNodeType) !== normalizeName(lnTypeId)) return false;
    var sameLdInst = !!(targetLdInst && rec.LDInst && isSameValue(rec.LDInst, targetLdInst));
    if (targetLdInst && rec.LDInst && !sameLdInst) return false;
    if (!sameLdInst && ctx && ctx.prefix && rec.Prefix && normalizeName(rec.Prefix) !== normalizeName(ctx.prefix)) return false;
    if (!sameLdInst && ctx && ctx.lnClass && rec.LNClass && normalizeName(rec.LNClass) !== normalizeName(ctx.lnClass)) return false;
    if (!sameLdInst && ctx && ctx.lnInst && rec.LNInst && normalizeName(rec.LNInst) !== normalizeName(ctx.lnInst)) return false;
    return true;
  });

  if (!records.length) return children;

  records.forEach(function (rec) {
    var fcdaLabel = "FCDA " + (rec.DAName || "") + (rec.fc ? " · fc=" + rec.fc : "");
    var extraInfo = [];
    if (rec.LDInst) extraInfo.push("ldInst=" + rec.LDInst);
    if (rec.Prefix) extraInfo.push("prefix=" + rec.Prefix);
    if (rec.LNClass) extraInfo.push("lnClass=" + rec.LNClass);
    if (rec.LNInst) extraInfo.push("lnInst=" + rec.LNInst);
    if (extraInfo.length) fcdaLabel += " [" + extraInfo.join(" · ") + "]";
    var fcdaAttrs = {
      doName: rec.DOName || "",
      daName: rec.DAName || "",
      fc: rec.fc || "",
      ldInst: rec.LDInst || "",
      prefix: rec.Prefix || "",
      lnClass: rec.LNClass || "",
      lnInst: rec.LNInst || "",
      lnType: rec.LNodeType || "",
      DOType: rec.DOType || "",
      DAType: rec.DAType || "",
      DAbType: rec.DAbType || "",
      CDC: rec.CDC || "",
    };
    var daChildAttrs = {
      name: rec.DAName || "",
      fc: rec.fc || "",
      type: rec.DAType || "",
      bType: rec.DAbType || "",
      ldInst: rec.LDInst || "",
      prefix: rec.Prefix || "",
      lnClass: rec.LNClass || "",
      lnInst: rec.LNInst || "",
      lnType: rec.LNodeType || "",
      doName: rec.DOName || "",
    };
    var daLabel = "DA " + (rec.DAName || "");
    var daExtraInfo = [];
    if (rec.LDInst) daExtraInfo.push("ldInst=" + rec.LDInst);
    if (rec.Prefix) daExtraInfo.push("prefix=" + rec.Prefix);
    if (rec.LNInst) daExtraInfo.push("lnInst=" + rec.LNInst);
    if (daExtraInfo.length) daLabel += " [" + daExtraInfo.join(" · ") + "]";
    children.push({
      text: fcdaLabel,
      icon: "fa fa-link",
      children: [
        {
          text: daLabel,
          icon: "fa fa-tag",
          children: [],
          state: { opened: false },
          a_attr: { title: daLabel },
          attributes: { tag: "DA_SYNTH", attrs: daChildAttrs },
          _meta: { tag: "DA_SYNTH", attrs: daChildAttrs },
        },
      ],
      state: { opened: false },
      a_attr: { title: fcdaLabel },
      attributes: { tag: "FCDA", attrs: fcdaAttrs },
      _meta: { tag: "FCDA", attrs: fcdaAttrs },
    });
  });

  return [
    {
      text: "FCDA",
      icon: "fa fa-link",
      children: children,
      state: { opened: false },
      a_attr: { title: "FCDA" },
      attributes: { tag: "FCDA_GROUP", attrs: { count: children.length } },
      _meta: { tag: "FCDA_GROUP", attrs: { count: children.length } },
    },
  ];
}

function buildDoTypeContenidoNode(doTypeId, ctx, contenidoLabel, includeFcda) {
  includeFcda = includeFcda !== false;
  var doTypeDef = getDoTypeDef(doTypeId);
  var label = contenidoLabel || "Contenido";
  var contenidoChildren = buildDoTypeDaBranchChildren(doTypeDef, ctx);
  var children = contenidoChildren.slice();
  if (includeFcda) {
    var fcdaBranch = buildDoTypeFcdaBranchNode(doTypeDef, ctx);
    if (fcdaBranch) {
      children.push(fcdaBranch);
    }
  }
  var nodeAttrs = {
    id: doTypeId || "",
    CDC: doTypeDef && doTypeDef.cdc ? doTypeDef.cdc : ""
  };
  if (ctx) {
    if (ctx.ldInst) nodeAttrs.ldInst = ctx.ldInst;
    if (ctx.prefix) nodeAttrs.prefix = ctx.prefix;
    if (ctx.lnClass) nodeAttrs.lnClass = ctx.lnClass;
    if (ctx.lnInst) nodeAttrs.lnInst = ctx.lnInst;
    if (ctx.lnType) nodeAttrs.lnType = ctx.lnType;
    if (ctx.doName) nodeAttrs.doName = ctx.doName;
  }
  return {
    text: label,
    icon: false,
    children: children,
    state: { opened: false },
    a_attr: { title: (doTypeDef && doTypeDef.cdc ? doTypeDef.cdc + " — " : "") + label },
    attributes: { tag: "DO_TYPE_CONTENT", attrs: nodeAttrs },
    _meta: {
      tag: "DO_TYPE_CONTENT",
      attrs: nodeAttrs,
      ctx: Object.assign({}, ctx || {}),
    },
  };
}

function buildDoTypeFcdaBranchNode(doTypeDef, ctx) {
  if (!doTypeDef || !doTypeDef.das || !doTypeDef.das.length) return null;
  var children = doTypeDef.das.map(function (da) {
    var daLabel = "DA " + (da.name || "") + (da.fc ? " · fc=" + da.fc : "") + (da.bType ? " · " + da.bType : "");
    var daTypeChildren = [];
    if (da.type && isStructDaEntry(da)) {
      var daTypeLabel = "DAType " + da.type;
      var daTypeBranch = {
        text: daTypeLabel,
        icon: "fa fa-tags",
        children: [],
        state: { opened: false },
        a_attr: { title: daTypeLabel },
        attributes: { tag: "DAType", attrs: { id: da.type } },
        _meta: { tag: "DAType", attrs: { id: da.type } },
      };
      if (daTypeIndex[da.type] && daTypeIndex[da.type].bdas && daTypeIndex[da.type].bdas.length) {
        daTypeBranch.children.push({
          text: "Contenido Datatype",
          icon: "fa fa-sitemap",
          children: buildDaTypeChildren(da, ctx),
          state: { opened: false },
          a_attr: { title: "Contenido Datatype" },
          attributes: { tag: "DA_TYPE_CONTENT", attrs: { id: da.type } },
          _meta: { tag: "DA_TYPE_CONTENT", attrs: { id: da.type } },
        });
      }
      daTypeChildren.push(daTypeBranch);
    }
    var daAttrs = Object.assign({ name: da.name, fc: da.fc, bType: da.bType, type: da.type, doName: ctx && ctx.doName ? ctx.doName : "" }, da.attrs || {});
    if (ctx) {
      if (ctx.ldInst) daAttrs.ldInst = ctx.ldInst;
      if (ctx.prefix) daAttrs.prefix = ctx.prefix;
      if (ctx.lnClass) daAttrs.lnClass = ctx.lnClass;
      if (ctx.lnInst) daAttrs.lnInst = ctx.lnInst;
      if (ctx.lnType) daAttrs.lnType = ctx.lnType;
    }
    return {
      text: daLabel,
      icon: "fa fa-tag",
      children: daTypeChildren,
      state: { opened: daTypeChildren.length > 0 || isStructDaEntry(da) },
      a_attr: { title: daLabel },
      attributes: { tag: "DA_SYNTH", attrs: daAttrs },
      _meta: { tag: "DA_SYNTH", attrs: daAttrs },
    };
  });
  return {
    text: "FCDA",
    icon: "fa fa-link",
    children: children,
    state: { opened: false },
    a_attr: { title: "FCDA" },
    attributes: { tag: "FCDA_SYNTH", attrs: { count: children.length } },
    _meta: { tag: "FCDA_SYNTH", attrs: { count: children.length } },
  };
}

function buildEnumTypeContenidoNode(enumId) {
  var enumDef = enumTypeIndex[enumId] || { vals: [] };
  return {
    text: "Contenido",
    icon: "fa fa-folder-open",
    children: (enumDef.vals || []).map(function (val) {
      return {
        text: (val.ord ? val.ord + " - " : "") + (val.text || ""),
        icon: "fa fa-circle",
        children: [],
        a_attr: { title: val.text || "" },
        attributes: { tag: "EnumVal", attrs: { ord: val.ord || "", type: enumId, text: val.text || "" } },
        _meta: { tag: "EnumVal", attrs: { ord: val.ord || "", type: enumId, text: val.text || "" } },
      };
    }),
    state: { opened: false },
    a_attr: { title: "Contenido EnumType: " + enumId },
    attributes: { tag: "ENUM_TYPE_CONTENT", attrs: { id: enumId } },
    _meta: { tag: "ENUM_TYPE_CONTENT", attrs: { id: enumId } },
  };
}

function buildDataTypeTemplatesTreeChildren(ctx) {
  var lnodeTypeChildren = [];
  Object.keys(lnodeTypeIndex).forEach(function (lnTypeId) {
    var lnt = lnodeTypeIndex[lnTypeId] || null;
    if (!lnt) return;

    var doChildren = [];
    var cdcLabel = (lnt.dos || [])
      .map(function (doEntry) {
        var doTypeDef = getDoTypeDef(doEntry.type);
        return doTypeDef && doTypeDef.cdc ? doTypeDef.cdc : "";
      })
      .filter(function (value) { return value; })
      .filter(function (value, index, all) { return all.indexOf(value) === index; })
      .join(" / ");

    function findCidReference(lnTypeId, doName, baseCtx) {
      if (!lnTypeId || !doName) return null;
      var candidates = [];
      var hasSpecificCtx = !!(
        baseCtx &&
        (baseCtx.ldInst || baseCtx.prefix || baseCtx.lnClass || baseCtx.lnInst)
      );
      for (var i = 0; i < lnRecords.length; i++) {
        var rec = lnRecords[i];
        if (!rec || rec.DOName !== doName) continue;
        if (rec.LNodeType && rec.LNodeType !== lnTypeId) continue;

        var score = 0;
        if (rec.LNodeType === lnTypeId) score += 5;
        if (baseCtx && baseCtx.ldInst) score += rec.LDInst === baseCtx.ldInst ? 5 : (rec.LDInst ? -2 : 0);
        if (baseCtx && baseCtx.prefix) score += rec.Prefix === baseCtx.prefix ? 4 : (rec.Prefix ? -2 : 0);
        if (baseCtx && baseCtx.lnClass) score += rec.LNClass === baseCtx.lnClass ? 3 : (rec.LNClass ? -1 : 0);
        if (baseCtx && baseCtx.lnInst) score += rec.LNInst === baseCtx.lnInst ? 3 : (rec.LNInst ? -1 : 0);
        candidates.push({ rec: rec, score: score });
      }

      if (!candidates.length) return null;
      candidates.sort(function (a, b) { return b.score - a.score; });

      if (hasSpecificCtx) {
        return candidates[0].score > 0 ? candidates[0].rec : null;
      }

      if (candidates.length === 1) return candidates[0].rec;

      var uniqueKeys = {};
      candidates.forEach(function (item) {
        var rec = item.rec || {};
        var key = [
          rec.LDInst || "",
          rec.Prefix || "",
          rec.LNClass || "",
          rec.LNInst || ""
        ].join("|");
        uniqueKeys[key] = true;
      });

      return Object.keys(uniqueKeys).length === 1 ? candidates[0].rec : null;
    }

    function buildDoChildren(baseCtx) {
      return (lnt.dos || []).map(function (doEntry) {
        var doLabel = "DO " + (doEntry.name || "");
        var doTypeDef = getDoTypeDef(doEntry.type);
        var cdc = doTypeDef ? doTypeDef.cdc : "";
        var effectiveCtx = Object.assign({}, ctx || {}, baseCtx || {});
        var cidRec = findCidReference(lnTypeId, doEntry.name || "", effectiveCtx);
        var doAttrs = {
          name: doEntry.name || "",
          type: doEntry.type || "",
          DOType: doEntry.type || "",
          CDC: cdc || "",
          lnType: lnTypeId,
          ldInst: effectiveCtx.ldInst || "",
          prefix: effectiveCtx.prefix || "",
          lnClass: effectiveCtx.lnClass || (lnt && lnt.lnClass) || "",
          lnInst: effectiveCtx.lnInst || ""
        };

        if (cidRec) {
          doAttrs.ldInst = doAttrs.ldInst || cidRec.LDInst || "";
          doAttrs.prefix = cidRec.Prefix || doAttrs.prefix || "";
          doAttrs.lnClass = cidRec.LNClass || doAttrs.lnClass || "";
          doAttrs.lnInst = cidRec.LNInst || doAttrs.lnInst || "";
          doAttrs.lnType = cidRec.LNodeType || doAttrs.lnType || "";
        }

        var doCtx = Object.assign({}, effectiveCtx, doAttrs, {
          doName: doEntry.name || "",
          lnDesc: effectiveCtx.lnDesc || "",
          desc: effectiveCtx.lnDesc || effectiveCtx.desc || "",
        });
        var doChildrenNodes = [buildDoTypeContenidoNode(doEntry.type, doCtx, "Contenido", false)];
        var doMeta = {
          tag: "DO_SYNTH",
          attrs: doAttrs,
          ctx: doCtx,
          doEntry: doEntry,
          doTypeDef: doTypeDef,
        };

        return {
          text: doLabel,
          icon: "fa fa-database",
          children: doChildrenNodes,
          state: { opened: false },
          a_attr: { title: doLabel + " → Contenido" },
          attributes: doMeta,
          _meta: doMeta,
        };
      });
    }

    doChildren = buildDoChildren(getDefaultLnContextForType(lnTypeId));

    var lnInstanceChildren = [];
    var lnInstances = {};

    lnRecords.forEach(function (rec) {
      if (!rec || rec.LNodeType !== lnTypeId) return;
      var prefix = rec.Prefix || "";
      var lnClassName = rec.LNClass || "";
      var lnInst = rec.LNInst || "";
      if (!lnClassName && !lnInst) return;
      var label = [prefix, lnClassName, lnInst].filter(function (v) { return String(v || "").trim(); }).join("");
      if (!label) return;
      var key = [rec.LDInst || "", prefix, lnClassName, lnInst].join("|");
      if (!lnInstances[key]) {
        lnInstances[key] = {
          ldInst: rec.LDInst || "",
          prefix: prefix,
          lnClass: lnClassName,
          lnInst: lnInst,
          lnDesc: rec.LNDesc || "",
          label: label,
        };
      }
    });

    if (!Object.keys(lnInstances).length) {
      flatNodes.forEach(function (node) {
        var attrs = node.attrs || {};
        if ((node.rawTag === "LN" || node.rawTag === "LN0") && (attrs.lnType === lnTypeId || attrs["lnType (CID)"] === lnTypeId)) {
          var rawLdInst = attrs.ldInst || getEffectiveLdInst(node.ctx || {}, attrs) || "";
          var prefix = attrs.prefix || "";
          var lnClassName = attrs.lnClass || attrs["lnClass (CID)"] || "";
          var lnInst = attrs.inst || attrs.lnInst || "";
          var rawLnDesc = attrs.desc || (node.ctx && (node.ctx.lnDesc || node.ctx.desc)) || "";
          var label = [prefix, lnClassName, lnInst].filter(function (v) { return String(v || "").trim(); }).join("");
          if (!label) return;
          var key = [rawLdInst, prefix, lnClassName, lnInst].join("|");
          if (!lnInstances[key]) {
            lnInstances[key] = {
              ldInst: rawLdInst,
              prefix: prefix,
              lnClass: lnClassName,
              lnInst: lnInst,
              lnDesc: rawLnDesc,
              label: label,
            };
          }
        }
      });
    }

    Object.keys(lnInstances).sort().forEach(function (key) {
      var item = lnInstances[key];
      var extra = [];
      if (item.ldInst) extra.push("LDInst: " + item.ldInst);
      if (item.prefix) extra.push("Prefix: " + item.prefix);
      var subtitle = extra.length ? " (" + extra.join(" · ") + ")" : "";
      var lnCtx = {
        ldInst: item.ldInst,
        prefix: item.prefix,
        lnClass: item.lnClass,
        lnInst: item.lnInst,
        lnType: lnTypeId,
        lnDesc: item.lnDesc || "",
        desc: item.lnDesc || "",
      };
      lnInstanceChildren.push({
        text: "LN " + item.label + subtitle,
        icon: "fa fa-layer-group",
        children: buildDoChildren(lnCtx),
        state: { opened: false },
        a_attr: { title: item.label + (subtitle ? " — " + extra.join(" · ") : "") },
        attributes: { tag: "LN_SYNTH", attrs: lnCtx, ctx: lnCtx },
        _meta: { tag: "LN_SYNTH", attrs: lnCtx, ctx: lnCtx },
      });
    });

    var lnodeTypeVisibleChildren = lnInstanceChildren.length ? lnInstanceChildren : doChildren;

    lnodeTypeChildren.push({
      text: "LNodeType " + ((lnt && lnt.lnClass) ? lnt.lnClass : lnTypeId),
      icon: "fa fa-layer-group",
      children: lnodeTypeVisibleChildren,
      state: { opened: false },
      a_attr: { title: "LNodeType: " + lnTypeId },
      attributes: { tag: "LNodeType", attrs: { id: lnTypeId, lnClass: (lnt && lnt.lnClass) ? lnt.lnClass : "" } },
      _meta: { tag: "LNodeType", attrs: { id: lnTypeId, lnClass: (lnt && lnt.lnClass) ? lnt.lnClass : "" } },
    });
  });

  var doTypeChildren = [];
  Object.keys(doTypeIndex).forEach(function (doTypeId) {
    var doTypeDef = doTypeIndex[doTypeId] || {};
    var cdc = doTypeDef.cdc || "";
    var typeLabel = cdc ? cdc : doTypeId;
    doTypeChildren.push({
      text: typeLabel,
      icon: "fa fa-cube",
      children: [buildDoTypeContenidoNode(doTypeId, ctx, "contenido")],
      state: { opened: false },
      a_attr: { title: typeLabel },
      attributes: { tag: "DOType", attrs: { id: doTypeId, CDC: cdc } },
      _meta: { tag: "DOType", attrs: { id: doTypeId, CDC: cdc } },
    });
  });

  var enumTypeChildren = [];
  Object.keys(enumTypeIndex).forEach(function (enumId) {
    enumTypeChildren.push({
      text: "EnumType " + enumId,
      icon: "fa fa-list-alt",
      children: [buildEnumTypeContenidoNode(enumId)],
      state: { opened: false },
      a_attr: { title: "EnumType: " + enumId },
      attributes: { tag: "EnumType", attrs: { id: enumId } },
      _meta: { tag: "EnumType", attrs: { id: enumId } },
    });
  });

  lnodeTypeChildren.sort(function (a, b) {
    var aText = a.text || "";
    var bText = b.text || "";
    return aText.localeCompare(bText);
  });

  doTypeChildren.sort(function (a, b) {
    var aText = a.text || "";
    var bText = b.text || "";
    return aText.localeCompare(bText);
  });

  enumTypeChildren.sort(function (a, b) {
    var aText = a.text || "";
    var bText = b.text || "";
    return aText.localeCompare(bText);
  });

  lnodeTypeChildren = lnodeTypeChildren.filter(function (item) {
    var text = item.text || "";
    return text.toLowerCase().indexOf("private") === -1 && text.toLowerCase().indexOf("setting") === -1;
  });

  doTypeChildren = doTypeChildren.filter(function (item) {
    var text = item.text || "";
    return text.toLowerCase().indexOf("private") === -1 && text.toLowerCase().indexOf("setting") === -1;
  });

  return [
    {
      text: "LNode Type",
      icon: "fa fa-layer-group",
      children: lnodeTypeChildren,
      state: { opened: true },
      a_attr: { title: "LNode Type" },
      attributes: { tag: "LNTYPE_GROUP", attrs: {} },
      _meta: { tag: "LNTYPE_GROUP", attrs: {} },
    },
    {
      text: "EnumType",
      icon: "fa fa-list-alt",
      children: enumTypeChildren,
      state: { opened: false },
      a_attr: { title: "EnumType" },
      attributes: { tag: "ENUMTYPE_GROUP", attrs: {} },
      _meta: { tag: "ENUMTYPE_GROUP", attrs: {} },
    },
  ];
}

function buildDaTypeChildren(da, ctx) {
  var children = [];
  if (!da || !isStructDaEntry(da) || !da.type || !daTypeIndex[da.type]) return children;

  daTypeIndex[da.type].bdas.forEach(function (bda) {
    var bdaLabel = "BDA " + (bda.name || "") + (bda.fc ? " · fc=" + bda.fc : "") + (bda.bType ? " · " + bda.bType : "");
    var bdaAttrs = Object.assign({ name: bda.name, fc: bda.fc, bType: bda.bType, type: bda.type }, bda.attrs || {});
    if (ctx) {
      if (ctx.ldInst) bdaAttrs.ldInst = ctx.ldInst;
      if (ctx.prefix) bdaAttrs.prefix = ctx.prefix;
      if (ctx.lnClass) bdaAttrs.lnClass = ctx.lnClass;
      if (ctx.lnInst) bdaAttrs.lnInst = ctx.lnInst;
      if (ctx.lnType) bdaAttrs.lnType = ctx.lnType;
    }
    children.push({
      text: bdaLabel,
      icon: isStructBdaEntry(bda) ? "fa fa-folder-open" : "fa fa-circle",
      children: isStructBdaEntry(bda) ? [buildBdaContenidoNode(bda, ctx)] : [],
      state: { opened: isStructBdaEntry(bda) },
      a_attr: { title: bdaLabel },
      attributes: {
        tag: "BDA_SYNTH",
        attrs: bdaAttrs,
      },
      _meta: {
        tag: "BDA_SYNTH",
        attrs: bdaAttrs,
      },
    });
  });

  return children;
}

function buildBdaContenidoNode(bda, ctx) {
  var bdaAttrs = Object.assign(
    { name: bda && bda.name ? bda.name : "", fc: bda && bda.fc ? bda.fc : "", bType: bda && bda.bType ? bda.bType : "", type: bda && bda.type ? bda.type : "" },
    (bda && bda.attrs) || {}
  );
  if (ctx) {
    if (ctx.ldInst) bdaAttrs.ldInst = ctx.ldInst;
    if (ctx.prefix) bdaAttrs.prefix = ctx.prefix;
    if (ctx.lnClass) bdaAttrs.lnClass = ctx.lnClass;
    if (ctx.lnInst) bdaAttrs.lnInst = ctx.lnInst;
    if (ctx.lnType) bdaAttrs.lnType = ctx.lnType;
  }
  var children = buildBdaTreeChildren(bda, ctx);
  var bdaTitle = "Contenido BDA" + (bdaAttrs.name ? " · " + bdaAttrs.name : "");

  return {
    text: "Contenido BDA",
    icon: "fa fa-sitemap",
    children: children,
    state: { opened: children.length > 0 },
    a_attr: { title: bdaTitle },
    attributes: { tag: "BDA_CONTENT", attrs: bdaAttrs },
    _meta: { tag: "BDA_CONTENT", attrs: bdaAttrs, ctx: ctx ? Object.assign({}, ctx) : {} },
  };
}

function buildBdaTreeChildren(bda, ctx) {
  var children = [];
  if (!bda || !isStructBdaEntry(bda) || !bda.type || !daTypeIndex[bda.type]) return children;

  daTypeIndex[bda.type].bdas.forEach(function (nestedBda) {
    var nestedLabel = "BDA " + (nestedBda.name || "") + (nestedBda.fc ? " · fc=" + nestedBda.fc : "") + (nestedBda.bType ? " · " + nestedBda.bType : "");
    var nestedAttrs = Object.assign({ name: nestedBda.name, fc: nestedBda.fc, bType: nestedBda.bType, type: nestedBda.type }, nestedBda.attrs || {});
    if (ctx) {
      if (ctx.ldInst) nestedAttrs.ldInst = ctx.ldInst;
      if (ctx.prefix) nestedAttrs.prefix = ctx.prefix;
      if (ctx.lnClass) nestedAttrs.lnClass = ctx.lnClass;
      if (ctx.lnInst) nestedAttrs.lnInst = ctx.lnInst;
      if (ctx.lnType) nestedAttrs.lnType = ctx.lnType;
    }
    children.push({
      text: nestedLabel,
      icon: isStructBdaEntry(nestedBda) ? "fa fa-folder-open" : "fa fa-circle",
      children: isStructBdaEntry(nestedBda) ? [buildBdaContenidoNode(nestedBda, ctx)] : [],
      state: { opened: isStructBdaEntry(nestedBda) },
      a_attr: { title: nestedLabel },
      attributes: {
        tag: "BDA_SYNTH",
        attrs: nestedAttrs,
      },
      _meta: {
        tag: "BDA_SYNTH",
        attrs: nestedAttrs,
      },
    });
  });

  return children;
}

function buildRows(nodes) {
  var keysSet = {};
  nodes.forEach(function (n) {
    Object.keys(n.attrs).forEach(function (k) {
      keysSet[k] = 1;
    });
  });
  var keys = Object.keys(keysSet);
  var header = ["Elemento", "Nivel"].concat(keys);
  var rows = [header];
  nodes.forEach(function (n) {
    var indent = "";
    for (var i = 0; i < n.depth; i++) indent += "  ";
    indent += n.text;
    var row = [indent, n.depth];
    keys.forEach(function (k) {
      row.push(n.attrs[k] !== undefined ? n.attrs[k] : "");
    });
    rows.push(row);
  });
  return rows;
}

var PAL = [
  { hBg: "1F3864", hFg: "FFFFFF", rowA: "D1E4F2", rowB: "B2D1EA" },
  { hBg: "1A5C1B", hFg: "FFFFFF", rowA: "D6EFD8", rowB: "B9DDB6" },
  { hBg: "7B3300", hFg: "FFFFFF", rowA: "F7E5D0", rowB: "EEC6AC" },
  { hBg: "4B0082", hFg: "FFFFFF", rowA: "E7D4F3", rowB: "D2B7EA" },
  { hBg: "374151", hFg: "FFFFFF", rowA: "EEF2F6", rowB: "DCE6EC" },
  { hBg: "005C5C", hFg: "FFFFFF", rowA: "D5F0EE", rowB: "AEE3DD" },
  { hBg: "4A3800", hFg: "FFFFFF", rowA: "FFF1B8", rowB: "FFE380" },
  { hBg: "003366", hFg: "FFFFFF", rowA: "D0E0FF", rowB: "A5C4FF" },
];

function hashString(value) {
  var text = String(value || "");
  var hash = 0;
  for (var i = 0; i < text.length; i++) {
    hash = (hash * 31 + text.charCodeAt(i)) >>> 0;
  }
  return hash;
}

function getCidPalette(seed) {
  return PAL[hashString(String(seed || "CID")) % PAL.length];
}

function getCidHeaderStyle(seed) {
  var p = getCidPalette(seed);
  return {
    fill: { type: "pattern", pattern: "solid", fgColor: { argb: "FF" + p.hBg } },
    font: { bold: true, color: { argb: "FF" + p.hFg }, size: 11 },
  };
}

function getCidSeedFromSelection(selectedIds) {
  var seed = "";
  (selectedIds || []).forEach(function (id) {
    var node = treeSelectedNodes[id] || {};
    var attrs = node.attrs || {};
    var ctx = node.ctx || {};
    seed += "|" + (attrs["LNodeType (CID)"] || attrs.lnType || ctx.lnType || attrs["lnType (CID)"] || attrs.lnClass || attrs["lnClass (CID)"] || "");
  });
  return seed || "CID";
}

function getCidSeedFromRecords(records) {
  var seed = "";
  (records || []).forEach(function (record) {
    seed += "|" + (record.LNodeType || record.lnClassCID || record.lnType || record.CID || "");
  });
  return seed || "CID";
}

function ca(r, c) {
  return XLSX.utils.encode_cell({ r: r, c: c });
}

function autoWidth(rows) {
  if (!rows.length) return [];
  return rows[0].map(function (_, ci) {
    var max = String(rows[0][ci] || "").length;
    for (var ri = 1; ri < rows.length; ri++) {
      var v = rows[ri][ci];
      if (v != null) max = Math.max(max, String(v).length);
    }
    return { wch: Math.min(max + 4, 80) };
  });
}

function autoHeight(rows) {
  if (!rows.length) return [];
  return rows.map(function (row, ri) {
    if (ri === 0) return { hpt: 26 };
    var maxLen = row.reduce(function (max, cell) {
      var len = String(cell || "").length;
      return Math.max(max, len);
    }, 0);
    if (maxLen > 120) return { hpt: 52 };
    if (maxLen > 80) return { hpt: 40 };
    if (maxLen > 50) return { hpt: 32 };
    return { hpt: 24 };
  });
}

function applyStyles(ws, rows, hPalIdx) {
  var hp = PAL[hPalIdx % PAL.length],
    ncols = rows[0].length;
  ws["!cols"] = autoWidth(rows);
  ws["!rows"] = autoHeight(rows);
  ws["!freeze"] = {
    xSplit: 0,
    ySplit: 1,
    topLeftCell: "A2",
    activePane: "bottomLeft",
    state: "frozen",
  };
  for (var ci = 0; ci < ncols; ci++) {
    var cell = ws[ca(0, ci)];
    if (!cell) continue;
    cell.s = {
      font: { bold: true, color: { rgb: hp.hFg }, sz: 11 },
      fill: { fgColor: { rgb: hp.hBg }, pattern: "solid" },
      alignment: { horizontal: "center", vertical: "center", wrapText: true },
      border: {
        top: { style: "medium", color: { rgb: "444444" } },
        bottom: { style: "medium", color: { rgb: "444444" } },
        left: { style: "thin", color: { rgb: "888888" } },
        right: { style: "thin", color: { rgb: "888888" } },
      },
    };
  }
  for (var ri = 1; ri < rows.length; ri++) {
    var depth = rows[ri][1] || 0;
    var p = PAL[depth % PAL.length];
    var bg = ri % 2 === 0 ? p.rowB : p.rowA;
    for (var ci = 0; ci < ncols; ci++) {
      var cell = ws[ca(ri, ci)];
      if (!cell) continue;
      cell.s = {
        fill: { fgColor: { rgb: bg }, pattern: "solid" },
        font: { sz: 10, color: { rgb: "111111" }, bold: ci === 0 },
        alignment: { vertical: "top", horizontal: "left", wrapText: true },
        border: {
          top: { style: "hair", color: { rgb: "CCCCCC" } },
          bottom: { style: "hair", color: { rgb: "CCCCCC" } },
          left: { style: "hair", color: { rgb: "CCCCCC" } },
          right: { style: "hair", color: { rgb: "CCCCCC" } },
        },
      };
    }
    var lc = ws[ca(ri, 1)];
    if (lc)
      lc.s = {
        fill: { fgColor: { rgb: p.hBg }, pattern: "solid" },
        font: { sz: 10, bold: true, color: { rgb: p.hFg } },
        alignment: { horizontal: "center", vertical: "center", wrapText: true },
        border: {
          top: { style: "hair", color: { rgb: "CCCCCC" } },
          bottom: { style: "hair", color: { rgb: "CCCCCC" } },
          left: { style: "hair", color: { rgb: "CCCCCC" } },
          right: { style: "hair", color: { rgb: "CCCCCC" } },
        },
      };
  }
}

function applyDatasetStyles(ws, rows, hPalIdx) {
  var hp = PAL[hPalIdx % PAL.length],
    ncols = rows[0].length;
  ws["!cols"] = autoWidth(rows);
  ws["!rows"] = autoHeight(rows);
  ws["!freeze"] = {
    xSplit: 0,
    ySplit: 1,
    topLeftCell: "A2",
    activePane: "bottomLeft",
    state: "frozen",
  };
  for (var ci = 0; ci < ncols; ci++) {
    var cell = ws[ca(0, ci)];
    if (!cell) continue;
    cell.s = {
      font: { bold: true, color: { rgb: hp.hFg }, sz: 11 },
      fill: { fgColor: { rgb: hp.hBg }, pattern: "solid" },
      alignment: { horizontal: "center", vertical: "center", wrapText: true },
      border: {
        top: { style: "medium", color: { rgb: "444444" } },
        bottom: { style: "medium", color: { rgb: "444444" } },
        left: { style: "thin", color: { rgb: "888888" } },
        right: { style: "thin", color: { rgb: "888888" } },
      },
    };
  }
  var iedList = [];
  for (var ri = 1; ri < rows.length; ri++) {
    var ied = rows[ri][0] || "";
    if (iedList.indexOf(ied) === -1) iedList.push(ied);
    var iedIdx = iedList.indexOf(ied);
    var p = PAL[iedIdx % PAL.length];
    var bg = ri % 2 === 0 ? p.rowB : p.rowA;
    for (var ci = 0; ci < ncols; ci++) {
      var cell = ws[ca(ri, ci)];
      if (!cell) continue;
      var fill = { fgColor: { rgb: bg }, pattern: "solid" };
      var font = { sz: 10, color: { rgb: "111111" }, bold: ci === 0 };
      if (ci === 0) {
        fill = { fgColor: { rgb: p.hBg }, pattern: "solid" };
        font = { sz: 10, color: { rgb: p.hFg }, bold: true };
      }
      cell.s = {
        fill: fill,
        font: font,
        alignment: { vertical: "top", horizontal: "left", wrapText: true },
        border: {
          top: { style: "hair", color: { rgb: "CCCCCC" } },
          bottom: { style: "hair", color: { rgb: "CCCCCC" } },
          left: { style: "hair", color: { rgb: "CCCCCC" } },
          right: { style: "hair", color: { rgb: "CCCCCC" } },
        },
      };
    }
  }
}

function downloadWB(wb, filename) {
  try {
    XLSX.writeFile(wb, filename, { bookType: "xlsx", cellStyles: true });
  } catch (e) {
    var wbout = XLSX.write(wb, {
      bookType: "xlsx",
      type: "array",
      cellStyles: true,
    });
    var blob = new Blob([wbout], { type: "application/octet-stream" });
    saveBlobAs(blob, filename);
  }
}

function saveBlobAs(blob, filename) {
  if (typeof saveAs === "function") {
    saveAs(blob, filename);
    return;
  }
  if (window && typeof window.saveAs === "function") {
    window.saveAs(blob, filename);
    return;
  }
  var url = URL.createObjectURL(blob);
  var a = document.createElement("a");
  a.href = url;
  a.download = filename;
  document.body.appendChild(a);
  a.dispatchEvent(new MouseEvent("click", { bubbles: true, cancelable: true, view: window }));
  document.body.removeChild(a);
  URL.revokeObjectURL(url);
}

function exportWithSheetJS(filename, rows, sheetName) {
  var wb = XLSX.utils.book_new();
  var ws = XLSX.utils.aoa_to_sheet(rows);
  XLSX.utils.book_append_sheet(wb, ws, sheetName || "Sheet1");
  downloadWB(wb, filename);
}

function getDatasetSummaryRows() {
  var counts = {};
  lnRecords.forEach(function (record) {
    var name = String(record.DataSet || "").trim();
    if (!name) name = "— Sin DataSet —";
    counts[name] = (counts[name] || 0) + 1;
  });

  var names = Object.keys(counts).sort(function (a, b) {
    return a.localeCompare(b);
  });

  var rows = [["DataSet", "Cantidad"]];
  names.forEach(function (name) {
    rows.push([name, counts[name]]);
  });
  return rows;
}

function appendDatasetSummarySheetExcelJS(workbook) {
  if (!workbook || typeof workbook.addWorksheet !== "function") return;
  var summaryRows = getDatasetSummaryRows();
  var ws = workbook.addWorksheet("Resumen DataSet");

  ws.mergeCells("A1:B1");
  ws.getCell("A1").value = "Resumen de DataSet";
  ws.getCell("A1").font = { size: 13, bold: true, color: { argb: "FFFFFFFF" } };
  ws.getCell("A1").alignment = { horizontal: "center", vertical: "middle" };
  ws.getRow(1).height = 24;
  ws.getCell("A1").fill = { type: "pattern", pattern: "solid", fgColor: { argb: "FF14532D" } };

  ws.mergeCells("A2:B2");
  ws.getCell("A2").value = "Ordenado por nombre de DataSet";
  ws.getCell("A2").font = { size: 10, italic: true, color: { argb: "FFCBD5E1" } };
  ws.getCell("A2").alignment = { horizontal: "left", vertical: "middle" };

  var headerRow = ws.addRow(summaryRows[0]);
  headerRow.font = { bold: true, color: { argb: "FFF0FDF4" } };
  headerRow.fill = { type: "pattern", pattern: "solid", fgColor: { argb: "FF166534" } };
  headerRow.alignment = { horizontal: "left", vertical: "middle" };

  for (var i = 1; i < summaryRows.length; i++) {
    ws.addRow(summaryRows[i]);
  }

  ws.getColumn(1).width = 34;
  ws.getColumn(2).width = 14;
  ws.views = [{ state: "frozen", ySplit: 3 }];
}

function appendDatasetSummarySheetSheetJS(wb) {
  if (!wb) return;
  var summaryRows = getDatasetSummaryRows();
  var ws = XLSX.utils.aoa_to_sheet([ ["Resumen de DataSet"], ["Ordenado por nombre de DataSet"], [] ]);
  XLSX.utils.sheet_add_aoa(ws, summaryRows, { origin: "A4" });
  XLSX.utils.book_append_sheet(wb, ws, "Resumen DataSet");
}

function exportTree() {
  if (!flatNodes.length) {
    alert("Sube un archivo primero.");
    return;
  }
  try {
    setStatus("Generando árbol Excel...");
    var wb = XLSX.utils.book_new();
    var fullRows = buildRows(flatNodes);
    var wsFull = XLSX.utils.aoa_to_sheet(fullRows);
    applyStyles(wsFull, fullRows, 0);
    XLSX.utils.book_append_sheet(wb, wsFull, "Arbol Completo");
    var d1 = [];
    for (var i = 0; i < flatNodes.length; i++) if (flatNodes[i].depth === 1) d1.push(i);
    for (var si = 0; si < d1.length; si++) {
      var start = d1[si],
        end = d1[si + 1] !== undefined ? d1[si + 1] : flatNodes.length;
      var slice = flatNodes.slice(start, end);
      if (!slice.length) continue;
      var rows = buildRows(slice);
      var ws = XLSX.utils.aoa_to_sheet(rows);
      applyStyles(ws, rows, si + 1);
      var name = (flatNodes[start].rawName || "Sec" + (si + 1))
        .replace(/[\\\/\?\*\[\]:]/g, "")
        .substring(0, 31);
      var fn = name;
      var at = 1;
      while (wb.SheetNames.indexOf(fn) !== -1)
        fn = name.substring(0, 28) + "_" + at++;
      XLSX.utils.book_append_sheet(wb, ws, fn);
    }
    downloadWB(wb, "CID_Arbol_IEC61850.xlsx");
    setStatus("✓ Árbol exportado.");
  } catch (ex) {
    setStatus("Error: " + ex.message);
    console.error(ex);
  }
}

function exportDatasetStyled() {
  if (!lnRecords.length) {
    alert("No se encontraron registros DO/LN.");
    return;
  }
  setStatus("Generando Dataset Excel (igual al sistema)...");
  if (typeof ExcelJS === "undefined" || !ExcelJS.Workbook) {
    setStatus("ExcelJS no disponible: exportando con formato básico...");
    return exportDatasetStyledFallback();
  }
  try {
    var workbook = new ExcelJS.Workbook();
    workbook.creator = "CID Tool";
    workbook.created = new Date();
    var cidHeaderStyle = getCidHeaderStyle(getCidSeedFromRecords(lnRecords));
    var ws = workbook.addWorksheet("Dataset");

    ws.mergeCells("A1:S1");
    ws.getCell("A1").value = "CID Dataset";
    ws.getCell("A1").font = { size: 14, bold: true, color: { argb: "FFFFFFFF" } };
    ws.getCell("A1").alignment = { horizontal: "center", vertical: "middle" };
    ws.getRow(1).height = 28;
    ws.getCell("A1").fill = { type: "pattern", pattern: "solid", fgColor: { argb: "FF059669" } };

    ws.mergeCells("A2:S2");
    ws.getCell("A2").value = "Generado: " + new Date().toLocaleString();
    ws.getCell("A2").font = { size: 10, italic: true, color: { argb: "FFCCCCCC" } };
    ws.getCell("A2").alignment = { horizontal: "right", vertical: "middle" };

    var headers = [
      "IED",
      "DataSet",
      "LDIns",
      "Prefix",
      "LNClass",
      "LNInst",
      "lnClass (CID)",
      "DOName",
      "DAType",
      "CDC",
      "DAName",
      "Tag",
      "CONCAT",
    ];

    ws.addRow([]);
    var headerRow = ws.addRow(headers);
    headerRow.font = cidHeaderStyle.font;
    headerRow.fill = cidHeaderStyle.fill;
    headerRow.alignment = { horizontal: "center", vertical: "middle", wrapText: true };
    ws.getRow(3).height = 20;

    lnRecords.forEach(function (r) {
      var row = [
        r.IED || "",
        r.DataSet || "",
        r.LDInst || "",
        r.Prefix || "",
        r.LNClass || "",
        r.LNInst || "",
        r.lnClassCID || "",
        r.DOName || "",
        r.DAType || "",
        r.CDC || "",
        r.DAName || "",
        r.Tag || "",
        r.CONCAT || "",
      ];
      // For FCDA, only show fields that have values
      if (r.Tag === "FCDA") {
        row = [
          r.IED || "",
          r.DataSet || "",
          r.LDInst || "",
          r.Prefix || "",
          r.LNClass || "",
          r.LNInst || "",
          r.lnClassCID || "",
          r.DOName || "",
          r.DAType || "",
          r.CDC || "",
          r.DAName || "",
          r.Tag || "",
          r.CONCAT || "",
        ];
      }
      ws.addRow(row);
    });

    applyExcelAutoFit(ws, 12);
    applyExcelFrame(ws, "FF334155");
    ws.views = [{ state: "frozen", xSplit: 0, ySplit: 3 }];

    appendDatasetSummarySheetExcelJS(workbook);

    workbook.xlsx.writeBuffer().then(function (buffer) {
      saveBlobAs(new Blob([buffer], { type: "application/octet-stream" }), "CID_Dataset.xlsx");
      setStatus("✓ Dataset exportado igual al sistema. " + lnRecords.length + " registros.");
    });
  } catch (ex) {
    setStatus("Error: " + ex.message);
    console.error(ex);
  }
}

var SUPABASE_URL = "https://ubtzbcmulanwirqbtxge.supabase.co/rest/v1/"; // Cambia esto por tu URL de Supabase
var SUPABASE_ANON_KEY = "sb_publishable_hog915kTgt6q-Pdre59Aew_ujhsgyxa"; // Cambia esto por tu clave pública ANON (o service_role si lo deseas en un entorno seguro)
var SUPABASE_TABLE = "cid_dataset"; // Cambia esto por el nombre de la tabla en Supabase

function buildSupabaseEndpoint(tableName) {
  var url = String(SUPABASE_URL || "").replace(/\/$/, "");
  if (!url) return "";
  if (url.match(/\/rest\/v\d+$/i)) {
    return url + "/" + tableName;
  }
  if (url.match(/\/rest\/v\d+\/$/i)) {
    return url + tableName;
  }
  return url + "/rest/v1/" + tableName;
}

function getSupabasePayload() {
  return {
    source: "IEC61850-CID-Tool",
    timestamp: new Date().toISOString(),
    meta: {
      technicalKey: document.getElementById("meta-name") ? document.getElementById("meta-name").textContent : "",
      type: document.getElementById("meta-type") ? document.getElementById("meta-type").textContent : "",
      manufacturer: document.getElementById("meta-manufacturer") ? document.getElementById("meta-manufacturer").textContent : "",
      configVersion: document.getElementById("meta-config-version") ? document.getElementById("meta-config-version").textContent : "",
    },
    records: lnRecords || [],
  };
}

function uploadDatasetToSupabase() {
  if (!lnRecords.length) {
    alert("Carga un archivo primero para subir sus datos a Supabase.");
    return;
  }
  if (!SUPABASE_URL || !SUPABASE_ANON_KEY || !SUPABASE_TABLE) {
    alert("Configura SUPABASE_URL, SUPABASE_ANON_KEY y SUPABASE_TABLE en js/script-rapido.js antes de subir.");
    return;
  }

  setStatus("Subiendo datos a Supabase...");

  var endpoint = buildSupabaseEndpoint(SUPABASE_TABLE);
  var payload = getSupabasePayload();

  fetch(endpoint, {
    method: "POST",
    mode: "cors",
    headers: {
      "Content-Type": "application/json",
      "apikey": SUPABASE_ANON_KEY,
      "Authorization": "Bearer " + SUPABASE_ANON_KEY,
      "Prefer": "return=representation"
    },
    body: JSON.stringify(payload)
  })
    .then(function (response) {
      if (!response.ok) {
        return response.text().then(function (text) {
          throw new Error("HTTP " + response.status + " " + response.statusText + " - " + text);
        });
      }
      return response.json();
    })
    .then(function (data) {
      setStatus("✓ Datos subidos a Supabase correctamente.");
      alert("Subida a Supabase completada.");
      console.log("Supabase response:", data);
    })
    .catch(function (error) {
      console.error(error);
      setStatus("Error al subir a Supabase: " + error.message);
      alert("No se pudo subir a Supabase: " + error.message);
    });
}

function exportDatasetStyledFallback() {
  var rows = [];
  rows.push(["CID Dataset"]);
  rows.push(["Generado:", new Date().toLocaleString()]);
  rows.push([]);
  rows.push([
    "IED",
    "DataSet",
    "LDInst",
    "Prefix",
    "LNClass",
    "LNInst",
    "lnClass (CID)",
    "DOName",
    "DAType",
    "CDC",
    "DAName",
    "Tag",
    "CONCAT",
  ]);

  lnRecords.forEach(function (r) {
    rows.push([
      r.IED || "",
      r.DataSet || "",
      r.LDInst || "",
      r.Prefix || "",
      r.LNClass || "",
      r.LNInst || "",
      r.lnClassCID || "",
      r.DOName || "",
      r.DAType || "",
      r.CDC || "",
      r.DAName || "",
      r.Tag || "",
      r.CONCAT || "",
    ]);
  });

  var wb = XLSX.utils.book_new();
  var ws = XLSX.utils.aoa_to_sheet(rows);
  XLSX.utils.book_append_sheet(wb, ws, "Dataset");
  appendDatasetSummarySheetSheetJS(wb);
  downloadWB(wb, "CID_Dataset.xlsx");
  setStatus("✓ Dataset exportado (básico). " + lnRecords.length + " registros.");
}

function renderTree(data) {
  // Limpiar caché de optimización cuando se carga un nuevo archivo
  if (typeof clearCadenaEntriesCache === 'function') {
    clearCadenaEntriesCache();
  }
  
  try {
    if (window._cachedJstree || (window._cachedJstree = $("#jstree").jstree(true))) {
      $("#jstree").jstree("destroy");
    }
  } catch (e) {
    // ignore if no tree exists yet
  }
  $("#jstree").jstree({
    core: {
      data: data,
      themes: { dots: true, icons: true },
    },
    checkbox: {
      keep_selected_style: true,
      three_state: false,
    },
    plugins: ["checkbox"],
  });
  window._cachedJstree = null; // reset cache on tree rebuild
  
  // ── Cache de instancia jstree ──────────────────────────
  var _jstreeCache = null;
  function getTree() {
    if (_jstreeCache) return _jstreeCache;
    _jstreeCache = window._cachedJstree || (window._cachedJstree = $("#jstree").jstree(true));
    return _jstreeCache;
  }
  $("#jstree").on("destroy.jstree", function() { _jstreeCache = null; });

  // ── Debounce helper ────────────────────────────────────
  function debounce(fn, ms) {
    var timer;
    return function() {
      clearTimeout(timer);
      timer = setTimeout(fn, ms);
    };
  }

  function syncTreeSelection() {
    treeSelectedNodes = {};
    var tree = getTree();
    if (!tree) return;
    var checkedNodes = tree.get_checked(true) || [];
    checkedNodes.forEach(function (node) {
      if (!node || !node.original) return;
      var nodeTagCheck = String(node.original._meta ? node.original._meta.tag || "" : "").toUpperCase();
      if (nodeTagCheck === "ENUMTYPE" || nodeTagCheck === "ENUMVAL") return;
      var parentIds = Array.isArray(node.parents) ? node.parents.filter(function (pid) { return pid && pid !== "#"; }) : [];
      var parentPath = parentIds.map(function (pid) {
        var pn = tree.get_node(pid);
        return pn && pn.text ? pn.text : "";
      }).filter(Boolean).concat([node.text]).join(" / ");
      treeSelectedNodes[node.id] = enrichStoredTreeNode(
        {
          text: node.text,
          tag: node.original._meta ? node.original._meta.tag : "",
          attrs: node.original._meta ? Object.assign({}, node.original._meta.attrs || {}) : {},
          ctx: node.original._meta ? Object.assign({}, node.original._meta.ctx || {}) : {},
          label: node.text,
          parentIds: parentIds,
          parentPath: parentPath,
        },
        node.id
      );
    });
    var newIds = checkedNodes.map(function(n){ return n.id; });
    treeSelectedOrder = newIds.slice();
    pruneCadenaExcludedRows(newIds);
    if (typeof scheduleUpdateTreeSelectionDisplay === 'function') {
      scheduleUpdateTreeSelectionDisplay();
    } else {
      updateTreeSelectionDisplay();
    }
    if (checkedNodes.length > 0) setStatus("Se actualizaron los elementos seleccionados del árbol.");
  }

  var syncTreeSelectionDebounced = debounce(syncTreeSelection, 120);

  function openNodeDescendants(tree, node) {
    if (!tree || !node || !node.children || !node.children.length) return;
    node.children.forEach(function (childId) {
      var childNode = tree.get_node(childId);
      if (!childNode) return;
      tree.open_node(childNode);
    });
  }

  function selectNodeDescendants(tree, node) {
    if (!tree || !node || !Array.isArray(node.children) || !node.children.length) return;

    var skipTags = {
      DO_TYPE_GROUP: true,
      LNTYPE_GROUP: true,
      ENUMTYPE_GROUP: true,
      FCDA_GROUP: true,
    };

    function walkChild(childNode) {
      if (!childNode || !childNode.original || !childNode.original._meta) return;
      var childTag = String(childNode.original._meta.tag || "").toUpperCase();
      if (skipTags[childTag]) return;

      try {
        tree.check_node(childNode);
      } catch (e) {}

      var childParentIds = Array.isArray(childNode.parents)
        ? childNode.parents.filter(function (pid) { return pid && pid !== "#"; })
        : [];
      var childParentPath = childParentIds
        .map(function (pid) {
          var parent = tree.get_node(pid);
          return parent && parent.text ? parent.text : "";
        })
        .filter(function (part) { return Boolean(part); })
        .concat([childNode.text])
        .join(" /");

      treeSelectedNodes[childNode.id] = enrichStoredTreeNode(
        {
          text: childNode.text,
          tag: childTag,
          attrs: Object.assign({}, childNode.original._meta.attrs || {}),
          ctx: Object.assign({}, childNode.original._meta.ctx || {}),
          label: childNode.text,
          parentIds: childParentIds,
          parentPath: childParentPath,
        },
        childNode.id
      );
      if (treeSelectedOrder.indexOf(childNode.id) === -1) treeSelectedOrder.push(childNode.id);

      if (childNode.children && childNode.children.length) {
        childNode.children.forEach(function (grandChildId) {
          walkChild(tree.get_node(grandChildId));
        });
      }
    }

    node.children.forEach(function (childId) {
      walkChild(tree.get_node(childId));
    });
  }

  function uncheckNodeDescendants(tree, node) {
    if (!tree || !node || !Array.isArray(node.children) || !node.children.length) return;

    var skipTags = {
      DO_TYPE_GROUP: true,
      LNTYPE_GROUP: true,
      ENUMTYPE_GROUP: true,
      FCDA_GROUP: true,
    };

    function walkChild(childNode) {
      if (!childNode || !childNode.original || !childNode.original._meta) return;
      var childTag = String(childNode.original._meta.tag || "").toUpperCase();
      if (skipTags[childTag]) return;

      try {
        tree.uncheck_node(childNode);
      } catch (e) {}
      delete treeSelectedNodes[childNode.id];
      var orderIdx = treeSelectedOrder.indexOf(childNode.id);
      if (orderIdx !== -1) treeSelectedOrder.splice(orderIdx, 1);

      if (childNode.children && childNode.children.length) {
        childNode.children.forEach(function (grandChildId) {
          walkChild(tree.get_node(grandChildId));
        });
      }
    }

    node.children.forEach(function (childId) {
      walkChild(tree.get_node(childId));
    });
  }

  function removeNodeFromTreeSelection(nodeId) {
    if (!nodeId) return;
    delete treeSelectedNodes[nodeId];
    var orderIdx = treeSelectedOrder.indexOf(nodeId);
    if (orderIdx !== -1) treeSelectedOrder.splice(orderIdx, 1);
  }

  function isSelectionCascadeNode(tag) {
    tag = String(tag || "").toUpperCase();
    return tag === "DO" || tag === "DO_SYNTH" || tag === "DO_TYPE_CONTENT" ||
      tag === "LN" || tag === "LN0" || tag === "LN_SYNTH" || tag === "LNODETYPE";
  }

  $("#jstree").on("select_node.jstree", function (e, data) {
    var node = data.node;
    var meta = node && node.original && node.original._meta;

    var jstreeInstance = window._cachedJstree || (window._cachedJstree = $("#jstree").jstree(true));
    var nodeTag = meta && meta.tag ? String(meta.tag || "").toUpperCase() : "";

    // Block check for all "Contenido" grouping nodes - they are navigation only
    var CONTENIDO_TAGS = ["DO_TYPE_CONTENT","DA_TYPE_CONTENT","BDA_CONTENT","DO_TYPE_GROUP","LNTYPE_GROUP","ENUMTYPE_GROUP","FCDA_GROUP"];
    var nodeText = node.text ? node.text.trim().toLowerCase() : "";
    var isContenidoNode = CONTENIDO_TAGS.indexOf(nodeTag) !== -1 ||
      nodeText === "contenido" ||
      nodeText === "contenido datatype" ||
      nodeText === "contenido bda" ||
      nodeText.indexOf("contenido") === 0;

    if (isContenidoNode) {
      if (jstreeInstance) {
        jstreeInstance.uncheck_node(node);
        if (node.children && node.children.length) {
          jstreeInstance.open_node(node);
        }
      }
      return;
    }

    currentNodeMeta = Object.assign({ nodeId: node && node.id ? node.id : "" }, meta);
    renderDetail(meta);

    if (typeof applyTreeCheckedHighlights === 'function') {
      applyTreeCheckedHighlights(jstreeInstance);
    }

    // Auto-check the node visually when selecting LN nodes inside a LNodeType
    if (jstreeInstance && node && (
      nodeTag === "LN_SYNTH" ||
      nodeTag === "LN" ||
      nodeTag === "LN0"
    )) {
      var isChecked = jstreeInstance.is_checked(node);
      if (!isChecked) {
        jstreeInstance.check_node(node);
      }
    }
    if (
      jstreeInstance &&
      node &&
      node.children &&
      node.children.length &&
      (nodeTag === "SDO" || nodeTag === "SDO_SYNTH" || nodeTag === "DA" || nodeTag === "DA_SYNTH" || nodeTag === "DA_TYPE_CONTENT" || nodeTag === "DO_TYPE_CONTENT")
    ) {
      jstreeInstance.open_node(node);
      if (nodeTag === "DA" || nodeTag === "DA_SYNTH") {
        openNodeDescendants(jstreeInstance, node);
      }
    }

    if (node && node.original && node.original._meta) {
      var nodeId = node.id;
      var parentIds = Array.isArray(node.parents) ? node.parents.filter(function (pid) { return pid && pid !== "#"; }) : [];
      var parentPath = parentIds.map(function (pid) { return jstreeInstance && jstreeInstance.get_node(pid) && jstreeInstance.get_node(pid).text ? jstreeInstance.get_node(pid).text : ""; }).filter(function (part) { return part; }).concat([node.text]).join(" / ");
      
      // For FCDA, ensure LDInst, Prefix, LnInst are populated from context
      var nodeAttrs = Object.assign({}, node.original._meta.attrs || {});
      var nodeCtx = Object.assign({}, node.original._meta.ctx || {});
      var nodeTag = node.original._meta.tag || "";
      
      if (String(nodeTag).toUpperCase() === "FCDA") {
        // Ensure FCDA has LDInst, Prefix, LnInst from context
        if (!nodeAttrs.ldInst) nodeAttrs.ldInst = nodeCtx.ldInst || "";
        if (!nodeAttrs.prefix) nodeAttrs.prefix = nodeCtx.prefix || "";
        if (!nodeAttrs.lnClass) nodeAttrs.lnClass = nodeCtx.lnClass || "";
        if (!nodeAttrs.lnInst) nodeAttrs.lnInst = nodeCtx.lnInst || "";
        if (!nodeAttrs.lnType) nodeAttrs.lnType = nodeCtx.lnType || "";
      }
      
      // Apply FCDA matching condition for DO nodes when selecting
      var doName = nodeAttrs.doName || nodeAttrs.name || "";
      var daName = nodeAttrs.daName || "";
      var nodeTagUpper = String(nodeTag).toUpperCase();
      var lnType = nodeAttrs.lnType || nodeCtx.lnType || "";
      
      // Check if DO is within LNodeType by checking parent hierarchy
      var isUnderLNodeType = false;
      var jstreeInstance = window._cachedJstree || (window._cachedJstree = $("#jstree").jstree(true));
      if (jstreeInstance && nodeId) {
        var parentNode = jstreeInstance.get_node(node.parent);
        while (parentNode && parentNode.id && parentNode.id !== "#") {
          var parentMeta = parentNode.original && parentNode.original._meta;
          if (parentMeta) {
            var parentTag = String(parentMeta.tag || "").toUpperCase();
            if (parentTag === "LNODETYPE" || parentTag === "LN_SYNTH" || parentTag === "LNTYPE_GROUP") {
              isUnderLNodeType = true;
              break;
            }
          }
          parentNode = jstreeInstance.get_node(parentNode.parent);
        }
      }
      
      if ((nodeTagUpper === "DO" || nodeTagUpper === "DO_SYNTH" || nodeTagUpper === "DO_TYPE_CONTENT") && isUnderLNodeType && doName) {
        if (!nodeAttrs.ldInst && nodeCtx.ldInst) nodeAttrs.ldInst = nodeCtx.ldInst;
        var selectionFields = resolveSelectionFields(
          {
            tag: nodeTag,
            attrs: nodeAttrs,
            ctx: nodeCtx,
            parentIds: parentIds
          },
          nodeId
        );
        var bestFcdaMatch = findBestFcdaMatch(doName, lnType, nodeCtx, lnRecords, selectionFields.doTypeId || nodeAttrs.DOType || nodeAttrs.type || "");
        if (bestFcdaMatch && bestFcdaMatch.rec) {
          var matchingFcda = bestFcdaMatch.rec;
          if (!nodeAttrs.ldInst && matchingFcda.LDInst) nodeAttrs.ldInst = matchingFcda.LDInst;
          if (matchingFcda.Prefix) nodeAttrs.prefix = matchingFcda.Prefix;
          if (matchingFcda.LNInst) nodeAttrs.lnInst = matchingFcda.LNInst;
          if (matchingFcda.LNClass) nodeAttrs.lnClass = matchingFcda.LNClass;
          if (matchingFcda.IED) nodeCtx.iedName = matchingFcda.IED;
          if (matchingFcda.LNodeType) nodeAttrs.lnType = matchingFcda.LNodeType;
          if (matchingFcda.DOType) nodeAttrs.DOType = matchingFcda.DOType;
          if (matchingFcda.CDC) nodeAttrs.CDC = matchingFcda.CDC;

          if (node && node.original) {
            node.original._meta = node.original._meta || {};
            node.original._meta.attrs = nodeAttrs;
            node.original._meta.ctx = nodeCtx;
            node.original.attributes = node.original.attributes || {};
            node.original.attributes.attrs = nodeAttrs;
            node.original.attributes.ctx = nodeCtx;
            try {
              var treeInstance = window._cachedJstree || (window._cachedJstree = $("#jstree").jstree(true));
              if (treeInstance) treeInstance.redraw_node(node.id);
            } catch (e) {}
          }
        }
      }

      // NOTA: al hacer click en un DO dentro de un LN, se actualiza el panel
      // "Nodo" (ya hecho arriba con renderDetail) y además se agrega a la
      // tabla "Elementos Seleccionados del Árbol" del módulo Excel. No se
      // marca el checkbox ni se seleccionan descendientes ni se tocan las
      // exclusiones de cadena.
      if (nodeTagUpper === "DO" || nodeTagUpper === "DO_SYNTH") {
        if (typeof clearCadenaExclusionsForNode === 'function') {
          clearCadenaExclusionsForNode(node);
        }
        if (typeof clearCadenaPreviewHiddenEntries === 'function') {
          clearCadenaPreviewHiddenEntries();
        }
        if (typeof clearCadenaEntriesCache === 'function') {
          clearCadenaEntriesCache();
        }
        treeSelectedNodes[nodeId] = enrichStoredTreeNode(
          {
            text: node.text,
            tag: nodeTag,
            attrs: nodeAttrs,
            ctx: nodeCtx,
            label: node.text,
            parentIds: parentIds,
            parentPath: parentPath,
          },
          nodeId
        );
        if (treeSelectedOrder.indexOf(nodeId) === -1) treeSelectedOrder.push(nodeId);
        if (typeof scheduleUpdateTreeSelectionDisplay === 'function') {
          scheduleUpdateTreeSelectionDisplay();
        } else {
          updateTreeSelectionDisplay();
        }
        setStatus("Se actualizó la información del nodo DO.");
        return;
      }

      if ((nodeTagUpper === "DA_SYNTH" || nodeTagUpper === "DA") && nodeId) {
        var daSelectionBase = enrichCadenaBaseFromAncestors(
          resolveCadenaBase({ tag: nodeTag, attrs: nodeAttrs, ctx: nodeCtx, parentPath: parentPath, parentIds: parentIds }, nodeId),
          nodeId,
          nodeAttrs,
          nodeCtx
        );
        if (daSelectionBase.doName) nodeAttrs.doName = daSelectionBase.doName;
        if (daSelectionBase.sdoName) nodeAttrs.sdoName = daSelectionBase.sdoName;
        if (daSelectionBase.lnType) nodeAttrs.lnType = daSelectionBase.lnType;
        if (daSelectionBase.ldInst) nodeAttrs.ldInst = daSelectionBase.ldInst;
        if (daSelectionBase.prefix) nodeAttrs.prefix = daSelectionBase.prefix;
        if (daSelectionBase.lnClass) nodeAttrs.lnClass = daSelectionBase.lnClass;
        if (daSelectionBase.lnInst) nodeAttrs.lnInst = daSelectionBase.lnInst;
        if (daSelectionBase.doTypeId) nodeAttrs.DOType = daSelectionBase.doTypeId;
        nodeCtx = Object.assign({}, nodeCtx, {
          doName: daSelectionBase.doName || nodeCtx.doName || "",
          sdoName: daSelectionBase.sdoName || nodeCtx.sdoName || "",
          lnType: daSelectionBase.lnType || nodeCtx.lnType || "",
          ldInst: daSelectionBase.ldInst || nodeCtx.ldInst || "",
          prefix: daSelectionBase.prefix || nodeCtx.prefix || "",
          lnClass: daSelectionBase.lnClass || nodeCtx.lnClass || "",
          lnInst: daSelectionBase.lnInst || nodeCtx.lnInst || "",
        });
      }

      if (typeof clearCadenaExclusionsForNode === 'function') {
        clearCadenaExclusionsForNode(node);
      }
      // Al re-seleccionar cualquier nodo, limpiar también las filas que
      // el usuario borró manualmente (cadenaPreviewRemovedRowKeys/EntryIds y
      // cadenaPreviewHiddenEntryIds). Esto garantiza que si el usuario borró
      // todas las filas y vuelve a hacer click en el mismo LN, la tabla
      // se muestra completa de nuevo en lugar de aparecer vacía.
      if (typeof clearCadenaPreviewHiddenEntries === 'function') {
        clearCadenaPreviewHiddenEntries();
      }
      if (typeof clearCadenaEntriesCache === 'function') {
        clearCadenaEntriesCache();
      }
      
      // EnumType y EnumVal no se agregan a la tabla de selección
      if (nodeTagUpper === "ENUMTYPE" || nodeTagUpper === "ENUMVAL") {
        var enumId = nodeAttrs.id || nodeAttrs.type || "";
        showEnumPanel(enumId);
        setStatus("EnumType: " + enumId);
        return;
      }

      // DAType/DOType (DataType) son nodos de definición/navegación — no se agregan a la tabla de selección
      if (nodeTagUpper === "DATYPE" || nodeTagUpper === "DOTYPE") {
        if (jstreeInstance) {
          try { jstreeInstance.uncheck_node(node); } catch (e) {}
          if (node.children && node.children.length) jstreeInstance.open_node(node);
        }
        setStatus("DataType: " + (nodeAttrs.id || nodeAttrs.type || node.text || ""));
        return;
      }

      // Cuando se selecciona un LN_SYNTH o LNodeType: marcar y agregar todos los DO hijos
      if (nodeTagUpper === "LN_SYNTH" || nodeTagUpper === "LNODETYPE" || nodeTagUpper === "LN" || nodeTagUpper === "LN0") {
        var tree2 = window._cachedJstree || (window._cachedJstree = $("#jstree").jstree(true));
        if (typeof enqueueOptimizedLnSelection === "function" && enqueueOptimizedLnSelection(tree2, node, nodeId, nodeTag, nodeAttrs, nodeCtx, parentIds, parentPath)) {
          return;
        }

        if (tree2) {
          tree2.open_node(node);
          treeSelectedNodes[nodeId] = enrichStoredTreeNode(
            {
              text: node.text,
              tag: nodeTag,
              attrs: nodeAttrs,
              ctx: nodeCtx,
              label: node.text,
              parentIds: parentIds,
              parentPath: parentPath,
            },
            nodeId
          );
          if (treeSelectedOrder.indexOf(nodeId) === -1) treeSelectedOrder.push(nodeId);
          pruneCadenaExcludedRows(getSelectedTreeIds());
          if (typeof scheduleUpdateTreeSelectionDisplay === 'function') {
            scheduleUpdateTreeSelectionDisplay();
          } else {
            updateTreeSelectionDisplay();
          }
          switchTab("excel");
          setStatus("Se seleccionó el nodo LN.");
        }
        return;
      }

      treeSelectedNodes[nodeId] = enrichStoredTreeNode(
        {
          text: node.text,
          tag: nodeTag,
          attrs: nodeAttrs,
          ctx: nodeCtx,
          label: node.text,
          parentIds: parentIds,
          parentPath: parentPath,
        },
        nodeId
      );
      if (treeSelectedOrder.indexOf(nodeId) === -1) treeSelectedOrder.push(nodeId);
      pruneCadenaExcludedRows(getSelectedTreeIds());
      if (typeof scheduleUpdateTreeSelectionDisplay === 'function') {
        scheduleUpdateTreeSelectionDisplay();
      } else {
        updateTreeSelectionDisplay();
      }
      
      // Automatically switch to Excel tab when a DO (Data Object) is selected
      if (nodeTagUpper === "DO" || nodeTagUpper === "DO_SYNTH") {
        switchTab('excel');
      }
      
      setStatus("Se actualizó la selección del árbol.");
    }
  });

  $("#jstree").on("activate_node.jstree", function (e, data) {
    var node = data && data.node ? data.node : null;
    if (!node || !treeSelectedNodes || !treeSelectedNodes[node.id]) return;

    if (typeof clearCadenaExclusionsForNode === 'function') {
      clearCadenaExclusionsForNode(node);
    }
    if (typeof clearCadenaEntriesCache === 'function') {
      clearCadenaEntriesCache();
    }

    pruneCadenaExcludedRows(getSelectedTreeIds());
    if (typeof scheduleUpdateTreeSelectionDisplay === 'function') {
      scheduleUpdateTreeSelectionDisplay();
    } else {
      updateTreeSelectionDisplay();
    }
  });

  $("#jstree").on("check_node.jstree", function (e, data) {
    if (window._suppressTreeSync) return;
    var tree = window._cachedJstree || (window._cachedJstree = $("#jstree").jstree(true));
    var checkedNode = data && data.node ? data.node : null;
    if (!checkedNode && tree && data && data.node) {
      try { checkedNode = tree.get_node(data.node); } catch (err) {}
    }
    if (checkedNode) clearCadenaExclusionsForNode(checkedNode);
    // Actualizar la selección sincronizada (debounced) para reflejar el
    // cambio de checkbox en `treeSelectedNodes` y la tabla de vista previa.
    if (typeof syncTreeSelectionDebounced === 'function') {
      syncTreeSelectionDebounced();
    }
    scheduleUpdateTreeSelectionDisplay();
    if (typeof applyTreeCheckedHighlights === 'function') {
      applyTreeCheckedHighlights(tree);
    }
  });

  $("#jstree").on("uncheck_node.jstree", function () {
    // Si fue un desmarcado programático desde removeCadenaPreviewRow, ignorar
    if (window._suppressTreeSync) return;
    var tree = window._cachedJstree || (window._cachedJstree = $("#jstree").jstree(true));
    var node = null;
    try {
      node = tree ? tree.get_node(arguments[1] && arguments[1].node ? arguments[1].node : null) : null;
    } catch (e) {
      node = arguments[1] && arguments[1].node ? arguments[1].node : null;
    }
    var nodeTag = node && node.original && node.original._meta ? String(node.original._meta.tag || "").toUpperCase() : "";
    if (tree && node && isSelectionCascadeNode(nodeTag)) {
      window._treeBulkUnchecking = true;
      removeNodeFromTreeSelection(node.id);
      excludeCadenaRowsForTreeNode(tree, node);
      uncheckNodeDescendants(tree, node);
      window._treeBulkUnchecking = false;
      setTimeout(function () {
        syncTreeSelection();
      }, 0);
      if (typeof applyTreeCheckedHighlights === 'function') {
        applyTreeCheckedHighlights(tree);
      }
      return;
    }
    if (window._treeBulkUnchecking) return;
    if (tree && node) {
      removeNodeFromTreeSelection(node.id);
      excludeCadenaRowsForTreeNode(tree, node);
      // Limpiar caché de entradas para forzar recálculo inmediato
      if (typeof clearCadenaEntriesCache === 'function') clearCadenaEntriesCache();
      // Sincronizar selección (debounced) para reconstruir treeSelectedNodes
      if (typeof syncTreeSelectionDebounced === 'function') {
        syncTreeSelectionDebounced();
      } else if (typeof syncTreeSelection === 'function') {
        syncTreeSelection();
      }
      scheduleUpdateTreeSelectionDisplay();
      if (typeof applyTreeCheckedHighlights === 'function') {
        applyTreeCheckedHighlights(tree);
      }
    }
  });

  // changed.jstree eliminado — se disparaba en cada click/scroll/apertura y congelaba la UI

  var CONTENIDO_TAGS_SET = {
    // Solo nodos agrupadores de navegación — sin checkbox
    "DO_TYPE_GROUP": true, "LNTYPE_GROUP": true, "ENUMTYPE_GROUP": true,
    "FCDA_GROUP": true,
    "ENUMTYPE": true, "DOTYPE": true, "DATYPE": true, "DA_TYPE_CONTENT": true
    // DA_TYPE_CONTENT, BDA_CONTENT, DO_TYPE_CONTENT son hijos seleccionables — conservan checkbox
  };

  function applyNoCheckboxClass() {
    setTimeout(function () {
      var tree = window._cachedJstree || (window._cachedJstree = $("#jstree").jstree(true));
      if (!tree) return;
      // Optimización: en vez de serializar el árbol lógico completo con
      // get_json (costoso en archivos grandes y repetido en cada apertura
      // de nodo), recorremos solo los <li> que jstree ya dibujó en el DOM.
      var liNodes = document.querySelectorAll("#jstree li.jstree-node");
      liNodes.forEach(function (li) {
        if (li.classList.contains("no-checkbox-li")) return;
        var jsNode = tree.get_node(li.id);
        if (!jsNode || !jsNode.original || !jsNode.original._meta) return;
        var tag = String(jsNode.original._meta.tag || "").toUpperCase();
        if (CONTENIDO_TAGS_SET[tag] || tag === "ENUMTYPE") {
          var anchor = document.getElementById(li.id + "_anchor");
          if (anchor) {
            anchor.classList.add("no-checkbox");
            var chk = anchor.querySelector(".jstree-checkbox, .jstree-undetermined, ins.jstree-checkbox, i.jstree-checkbox");
            if (chk) chk.parentNode.removeChild(chk);
          }
          li.classList.add("no-checkbox-li");
        }
      });
      if (typeof applyTreeCheckedHighlights === "function") {
        applyTreeCheckedHighlights(tree);
      }
    }, 0);
  }

  function applyTreeCheckedHighlights(tree) {
    tree = tree || (window._cachedJstree || (window._cachedJstree = $("#jstree").jstree(true)));
    if (!tree) return;

    var anchors = document.querySelectorAll("#jstree a.jstree-anchor");
    anchors.forEach(function (anchor) {
      anchor.classList.remove("tree-node-checked-highlight");
    });

    var selectedIds = Object.keys(treeSelectedNodes || {});
    if (!selectedIds.length) return;

    var activeNodeIds = {};
    if (typeof buildCadenaPreviewEntriesOptimized === 'function') {
      var entries = buildCadenaPreviewEntriesOptimized(selectedIds) || [];
      if (!entries.length) return;
      entries.forEach(function (entry) {
        if (entry && entry.nodeId) activeNodeIds[entry.nodeId] = true;
      });
    }

    function highlightNodeId(nodeId) {
      if (!nodeId) return;
      var anchor = document.getElementById(nodeId + "_anchor");
      if (anchor) anchor.classList.add("tree-node-checked-highlight");
    }

    function highlightDescendants(parentNode) {
      if (!parentNode || !Array.isArray(parentNode.children)) return;
      parentNode.children.forEach(function (childId) {
        highlightNodeId(childId);
        var childNode = tree.get_node(childId);
        if (childNode) {
          highlightDescendants(childNode);
        }
      });
    }

    Object.keys(treeSelectedNodes || {}).forEach(function (nodeId) {
      if (Object.keys(activeNodeIds).length && !activeNodeIds[nodeId]) return;
      highlightNodeId(nodeId);
      var node = tree.get_node(nodeId);
      if (node && node.original && node.original._meta) {
        var tag = String(node.original._meta.tag || "").toUpperCase();
        if (tag === "DO" || tag === "DO_SYNTH" || tag === "LN" || tag === "LN0" || tag === "LN_SYNTH" || tag === "LNODETYPE") {
          highlightDescendants(node);
        }
      }
    });
  }

  $("#jstree").on("ready.jstree", applyNoCheckboxClass);
  $("#jstree").on("open_node.jstree", applyNoCheckboxClass);
  $("#jstree").on("after_open.jstree", applyNoCheckboxClass);
  $("#jstree").on("load_node.jstree", applyNoCheckboxClass);
  $("#jstree").on("redraw.jstree", applyNoCheckboxClass);
  $("#jstree").on("refresh.jstree", applyNoCheckboxClass);
}

function refreshLNodeTypeDoCidAttributes() {
  var tree = window._cachedJstree || (window._cachedJstree = (window.jQuery && window.jQuery("#jstree").length ? window.jQuery("#jstree").jstree(true) : null));
  if (!tree || !Array.isArray(lnRecords) || !lnRecords.length) return;
  var flat = tree.get_json("#", { flat: true }) || [];
  var nodeById = {};
  flat.forEach(function (node) {
    if (node && node.id) nodeById[node.id] = node;
  });

  flat.forEach(function (node) {
    if (!node || !node.original || !node.original._meta) return;
    var tag = String(node.original._meta.tag || "").toUpperCase();
    var attrs = node.original._meta.attrs || {};
    var ctx = node.original._meta.ctx || {};
    var doName = attrs.doName || attrs.name || "";
    var daName = attrs.daName || "";
    
    // Check if DO is within LNodeType by checking parent hierarchy
    var isUnderLNodeType = false;
    if (node.id) {
      var parentNode = nodeById[node.parent] || null;
      while (parentNode && parentNode.id && parentNode.id !== "#") {
        var parentMeta = parentNode.original && parentNode.original._meta;
        if (parentMeta) {
          var parentTag = String(parentMeta.tag || "").toUpperCase();
          if (parentTag === "LNODETYPE" || parentTag === "LN_SYNTH" || parentTag === "LNTYPE_GROUP") {
            isUnderLNodeType = true;
            break;
          }
        }
        parentNode = nodeById[parentNode.parent] || null;
      }
    }
    
    // Apply FCDA matching condition for DO nodes belonging to LNodeType
    if ((tag === "DO" || tag === "DO_SYNTH" || tag === "DO_TYPE_CONTENT") && isUnderLNodeType && doName) {
      var bestFcdaMatch = findBestFcdaMatch(doName, attrs.lnType || ctx.lnType || "", ctx, lnRecords, attrs.DOType || attrs.type || "");
      var matchingFcda = bestFcdaMatch && bestFcdaMatch.rec ? bestFcdaMatch.rec : null;
      
      if (matchingFcda) {
        var updated = false;
        if (!attrs.ldInst && matchingFcda.LDInst) {
          attrs.ldInst = matchingFcda.LDInst;
          updated = true;
        }
        if (!attrs.prefix && matchingFcda.Prefix) {
          attrs.prefix = matchingFcda.Prefix;
          updated = true;
        }
        if (!attrs.lnInst && matchingFcda.LNInst) {
          attrs.lnInst = matchingFcda.LNInst;
          updated = true;
        }
        
        if (updated) {
          node.original._meta.attrs = attrs;
          node.original.attributes = node.original.attributes || {};
          node.original.attributes.attrs = attrs;
        }
      }
    }
    
    // Original DO_SYNTH logic (only for DO outside LNodeType)
    if (tag !== "DO_SYNTH") return;
    var parentNode = nodeById[node.parent] || null;
    var underLNodeType = false;
    while (parentNode && parentNode.original && parentNode.id) {
      var parentTag = String(parentNode.original._meta.tag || "").toUpperCase();
      if (parentTag === "LNODETYPE" || parentTag === "LN_SYNTH" || parentTag === "LNTYPE_GROUP") {
        underLNodeType = true;
        break;
      }
      parentNode = nodeById[parentNode.parent] || null;
    }
    if (underLNodeType) return;
    var lnTypeId = attrs.lnType || "";
    if (!lnTypeId || !doName) return;
    var cidRec = lnRecords.find(function (rec) {
      return rec && rec.LNodeType === lnTypeId && rec.DOName === doName && (rec.LDInst || rec.LNInst || rec.Prefix);
    });
    if (!cidRec) return;
    var updated = false;
    if (cidRec.LDInst && attrs.ldInst !== cidRec.LDInst) {
      attrs.ldInst = cidRec.LDInst;
      updated = true;
    }
    if (cidRec.Prefix && attrs.prefix !== cidRec.Prefix) {
      attrs.prefix = cidRec.Prefix;
      updated = true;
    }
    if (cidRec.LNClass && attrs.lnClass !== cidRec.LNClass) {
      attrs.lnClass = cidRec.LNClass;
      updated = true;
    }
    if (cidRec.LNInst && attrs.lnInst !== cidRec.LNInst) {
      attrs.lnInst = cidRec.LNInst;
      updated = true;
    }
    if (!updated && !buildDoFcdaBranchChildren(lnTypeId, doName, attrs).length) return;

    node.original._meta.attrs = attrs;
    node.original.attributes = node.original.attributes || {};
    node.original.attributes.attrs = attrs;
    node.original.a_attr = node.original.a_attr || {};
    var extra = [];
    if (attrs.ldInst) extra.push("LDInst: " + attrs.ldInst);
    if (attrs.prefix) extra.push("Prefix: " + attrs.prefix);
    if (attrs.lnInst) extra.push("LNInst: " + attrs.lnInst);
    node.original.a_attr.title = (node.text || "") + (extra.length ? " — " + extra.join(" · ") : "");

    var fcdaBranches = buildDoFcdaBranchChildren(lnTypeId, doName, attrs);
    if (fcdaBranches.length) {
      node.original.children = (node.original.children || []).filter(function (child) {
        return !(child && child._meta && String(child._meta.tag || "").toUpperCase() === "FCDA_GROUP");
      });
      node.original.children = node.original.children.concat(fcdaBranches);
    }

    tree.redraw_node(node.id);
  });

  flat.forEach(function (node) {
    if (!node || !node.original || !node.original._meta) return;
    if (String(node.original._meta.tag || "").toUpperCase() !== "DA_SYNTH") return;
    var attrs = node.original._meta.attrs || {};
    var parentNode = nodeById[node.parent] || null;
    while (parentNode && parentNode.original && String(parentNode.original._meta.tag || "").toUpperCase() !== "DO_SYNTH") {
      parentNode = nodeById[parentNode.parent] || null;
    }
    if (!parentNode || !parentNode.original || String(parentNode.original._meta.tag || "").toUpperCase() !== "DO_SYNTH") return;
    var doAttrs = parentNode.original._meta.attrs || {};
    var updated = false;
    if (doAttrs.ldInst && attrs.ldInst !== doAttrs.ldInst) {
      attrs.ldInst = doAttrs.ldInst;
      updated = true;
    }
    if (doAttrs.prefix && attrs.prefix !== doAttrs.prefix) {
      attrs.prefix = doAttrs.prefix;
      updated = true;
    }
    if (doAttrs.lnClass && attrs.lnClass !== doAttrs.lnClass) {
      attrs.lnClass = doAttrs.lnClass;
      updated = true;
    }
    if (doAttrs.lnInst && attrs.lnInst !== doAttrs.lnInst) {
      attrs.lnInst = doAttrs.lnInst;
      updated = true;
    }
    if (doAttrs.lnType && attrs.lnType !== doAttrs.lnType) {
      attrs.lnType = doAttrs.lnType;
      updated = true;
    }
    if (!updated) return;
    node.original._meta.attrs = attrs;
    node.original.attributes = node.original.attributes || {};
    node.original.attributes.attrs = attrs;
    node.original.a_attr = node.original.a_attr || {};
    var extra = [];
    if (attrs.ldInst) extra.push("LDInst: " + attrs.ldInst);
    if (attrs.prefix) extra.push("Prefix: " + attrs.prefix);
    if (attrs.lnInst) extra.push("LNInst: " + attrs.lnInst);
    node.original.a_attr.title = (node.text || "") + (extra.length ? " — " + extra.join(" · ") : "");
    tree.redraw_node(node.id);
  });
}

function expandAll() {
  try {
    $("#jstree").jstree("open_all");
  } catch (e) {}
}

function collapseAll() {
  try {
    $("#jstree").jstree("close_all");
  } catch (e) {}
}

function switchTab(tab) {
  var panelNode = document.getElementById("panel-node");
  var panelDataset = document.getElementById("panel-dataset");
  var panelExcel = document.getElementById("panel-excel");
  var panelEnum = document.getElementById("panel-enum");
  if (panelNode) panelNode.style.display = tab === "node" ? "block" : "none";
  if (panelDataset) panelDataset.style.display = tab === "dataset" ? "block" : "none";
  if (panelExcel) panelExcel.style.display = tab === "excel" ? "block" : "none";
  if (panelEnum) panelEnum.style.display = tab === "enum" ? "flex" : "none";

  var tabNode = document.getElementById("tab-node");
  var tabDataset = document.getElementById("tab-dataset");
  var tabExcel = document.getElementById("tab-excel");
  var tabEnum = document.getElementById("tab-enum");
  if (tabNode) tabNode.classList.toggle("active", tab === "node");
  if (tabDataset) tabDataset.classList.toggle("active", tab === "dataset");
  if (tabExcel) tabExcel.classList.toggle("active", tab === "excel");
  if (tabEnum) tabEnum.classList.toggle("active", tab === "enum");
}

function showEnumPanel(enumId) {
  var enumDef = enumTypeIndex[enumId];
  var tabEnum = document.getElementById("tab-enum");
  var badge = document.getElementById("enum-badge");
  var title = document.getElementById("enum-panel-title");
  var idSpan = document.getElementById("enum-panel-id");
  var content = document.getElementById("enum-panel-content");

  if (tabEnum) tabEnum.style.display = "";
  if (idSpan) idSpan.textContent = enumId ? "— " + enumId : "";
  if (title) title.textContent = "EnumType";

  if (!enumDef || !enumDef.vals || !enumDef.vals.length) {
    if (content) content.innerHTML = '<div style="color:#64748b;text-align:center;padding:30px;">Sin valores definidos para <b style="color:#a78bfa;">' + esc(enumId) + '</b></div>';
    if (badge) badge.textContent = "0";
    switchTab("enum");
    return;
  }

  if (badge) badge.textContent = enumDef.vals.length;

  var html = '<table style="width:100%;border-collapse:collapse;font-size:13px;">';
  html += '<thead><tr style="background:#4c1d95;position:sticky;top:0;z-index:2;">';
  html += '<th style="padding:9px 14px;text-align:center;color:#e9d5ff;font-weight:700;width:60px;">Ord</th>';
  html += '<th style="padding:9px 14px;text-align:left;color:#e9d5ff;font-weight:700;">Valor</th>';
  html += '</tr></thead><tbody>';

  enumDef.vals.forEach(function (val, idx) {
    var bg = idx % 2 === 0 ? "#1e1040" : "#150d35";
    html += '<tr style="background:' + bg + ';">';
    html += '<td style="padding:8px 14px;text-align:center;color:#c4b5fd;font-weight:700;border-bottom:1px solid #2e1065;">' + esc(val.ord) + '</td>';
    html += '<td style="padding:8px 14px;color:#f3e8ff;border-bottom:1px solid #2e1065;">' + esc(val.text) + '</td>';
    html += '</tr>';
  });

  html += '</tbody></table>';
  if (content) content.innerHTML = html;
  switchTab("enum");
}

function populateDatasetFilters() {
  var iedSel = document.getElementById("ds-filter-ied");
  var dsSel = document.getElementById("ds-filter-ds");
  if (!iedSel || !dsSel) return;
  var ieds = [],
    dsets = [];
  lnRecords.forEach(function (r) {
    if (r.IED && ieds.indexOf(r.IED) === -1) ieds.push(r.IED);
    if (r.DataSet && dsets.indexOf(r.DataSet) === -1) dsets.push(r.DataSet);
  });
  iedSel.innerHTML = '<option value="">— Todos los IED —</option>';
  ieds.forEach(function (v) {
    iedSel.innerHTML += '<option value="' + v + '">' + v + "</option>";
  });
  dsSel.innerHTML = '<option value="">— Todos los DataSet —</option>';
  dsets.forEach(function (v) {
    dsSel.innerHTML += '<option value="' + v + '">' + v + "</option>";
  });
}

function renderDatasetSheet() {
  var tbody = document.getElementById("dataset-sheet-tbody");
  var countLabel = document.getElementById("dataset-sheet-count");
  if (!tbody) return;

  var counts = {};
  lnRecords.forEach(function (record) {
    var name = String(record.DataSet || "").trim();
    if (!name) name = "— Sin DataSet —";
    counts[name] = (counts[name] || 0) + 1;
  });

  var names = Object.keys(counts).sort(function (a, b) {
    return a.localeCompare(b);
  });

  if (countLabel) {
    countLabel.textContent = names.length + (names.length === 1 ? " dataset" : " datasets");
  }

  if (!names.length) {
    tbody.innerHTML = '<tr><td colspan="2" class="dataset-sheet-empty">Carga un archivo para ver el resumen de datasets</td></tr>';
    return;
  }

  var html = "";
  names.forEach(function (name) {
    html += "<tr>" +
      "<td>" + esc(name) + "</td>" +
      "<td>" + esc(counts[name]) + "</td>" +
      "</tr>";
  });
  tbody.innerHTML = html;
}

function filterDataset() {
  var q = (document.getElementById("ds-search").value || "").toLowerCase();
  var ied = document.getElementById("ds-filter-ied").value;
  var ds = document.getElementById("ds-filter-ds").value;
  var filtered = lnRecords.filter(function (r) {
    if (ied && r.IED !== ied) return false;
    if (ds && r.DataSet !== ds) return false;
    if (q) {
      var line = r._searchText || buildDatasetSearchText(r);
      if (line.indexOf(q) === -1) return false;
    }
    return true;
  });
  renderDatasetTable(filtered);
  updateDatasetSelectionDisplay();
}

function requestDatasetFilter() {
  if (datasetFilterTimer) clearTimeout(datasetFilterTimer);
  datasetFilterTimer = setTimeout(function () {
    datasetFilterTimer = null;
    filterDataset();
  }, 120);
}

function createDatasetKey(index, record) {
  return index + "_" + (record.CONCAT || record.IED || "");
}

function renderDatasetTable(records) {
  var token = ++datasetRenderToken;
  datasetDisplayRecords = records;
  var badge = document.getElementById("ds-badge");
  if (badge) badge.textContent = records.length;
  var tbody = document.getElementById("ds-tbody");
  if (!tbody) return;
  if (!records.length) {
    tbody.innerHTML =
      '<tr><td colspan="12" style="color:#64748b;text-align:center;padding:20px">Sin registros</td></tr>';
    return;
  }
  tbody.innerHTML = "";

  var batchSize = 250;
  var index = 0;

  function appendBatch() {
    if (token !== datasetRenderToken) return;
    var html = "";
    var end = Math.min(index + batchSize, records.length);
    for (; index < end; index++) {
      var r = records[index];
      html += "<tr>" +
        "<td>" +
        esc(r.IED) +
        "</td>" +
        "<td>" +
        esc(r.LDInst) +
        "</td>" +
        "<td>" +
        esc(r.Prefix) +
        "</td>" +
        "<td><b>" +
        esc(r.LNClass) +
        "</b></td>" +
        "<td>" +
        esc(r.LNInst) +
        "</td>" +
        '<td style="color:#cbd5e1;font-size:11px;max-width:180px;overflow:hidden;text-overflow:ellipsis" title="' +
        esc(r.lnClassCID || "") +
        '">' +
        esc(r.lnClassCID || "") +
        "</td>" +
        "<td>" +
        esc(r.DOName) +
        "</td>" +
        '<td style="color:#c4b5fd;font-size:11px;max-width:140px;overflow:hidden;text-overflow:ellipsis" title="' +
        esc(r.DAType || "") +
        '">' +
        esc(r.DAType || "") +
        "</td>" +
        "<td>" +
        esc(r.DAName || "") +
        "</td>" +
        '<td><span class="dataset-badge ' + getFcBadgeClass(r.fc) + '">' +
        esc(r.fc || "") +
        "</span></td>" +
        '<td><span class="dataset-badge ' + getTagBadgeClass(r.Tag) + '">' +
        esc(r.Tag) +
        "</span></td>" +
        '<td style="color:#34d399;font-weight:700;font-family:monospace">' +
        esc(r.CONCAT || "") +
        "</td>" +
        "</tr>";
    }
    tbody.insertAdjacentHTML("beforeend", html);
    if (index < records.length) {
      requestAnimationFrame(appendBatch);
    } else {
      updateSelectedCount();
    }
  }

  requestAnimationFrame(appendBatch);
}


function setHeaderMetaValue(id, value) {
  var el = document.getElementById(id);
  if (el) el.textContent = value || "—";
}

function sanitizeFileNamePart(value) {
  return String(value || "")
    .trim()
    .replace(/[\\/:*?"<>|]+/g, "_")
    .replace(/\s+/g, "_")
    .replace(/_+/g, "_")
    .replace(/^_+|_+$/g, "");
}

function getCadenaExportFileName() {
  var technicalKeyEl = document.getElementById("meta-name");
  var technicalKey = technicalKeyEl ? String(technicalKeyEl.textContent || "").trim() : "";
  var cleanKey = sanitizeFileNamePart(technicalKey) || "CID";
  return "CADENA_" + cleanKey + ".xlsx";
}

function getTreeSelectionExportMetaRows() {
  var technicalKeyEl = document.getElementById("meta-name");
  var typeEl = document.getElementById("meta-type");
  var manufacturerEl = document.getElementById("meta-manufacturer");
  var versionEl = document.getElementById("meta-config-version");
  var now = new Date();

  return [
    ["Campo", "Valor"],
    ["Technical Key", technicalKeyEl ? String(technicalKeyEl.textContent || "").trim() : ""],
    ["Tipo", typeEl ? String(typeEl.textContent || "").trim() : ""],
    ["Fabricante", manufacturerEl ? String(manufacturerEl.textContent || "").trim() : ""],
    ["Versión", versionEl ? String(versionEl.textContent || "").trim() : ""],
    ["Fecha", now.toLocaleDateString()],
    ["Hora", now.toLocaleTimeString()],
  ];
}

function appendTreeSelectionMetaSheetExcelJS(workbook) {
  if (!workbook || typeof workbook.addWorksheet !== "function") return;

  var metaRows = getTreeSelectionExportMetaRows();
  var ws = workbook.addWorksheet("Metadatos");

  ws.mergeCells("A1:B1");
  ws.getCell("A1").value = "Elementos Seleccionados del Árbol";
  ws.getCell("A1").font = { size: 13, bold: true, color: { argb: "FFFFFFFF" } };
  ws.getCell("A1").alignment = { horizontal: "center", vertical: "middle" };
  ws.getRow(1).height = 24;
  ws.getCell("A1").fill = { type: "pattern", pattern: "solid", fgColor: { argb: "FF14532D" } };

  ws.mergeCells("A2:B2");
  ws.getCell("A2").value = "Datos del archivo al momento de la descarga";
  ws.getCell("A2").font = { size: 10, italic: true, color: { argb: "FFCBD5E1" } };
  ws.getCell("A2").alignment = { horizontal: "left", vertical: "middle" };

  var headerRow = ws.addRow(metaRows[0]);
  headerRow.font = { bold: true, color: { argb: "FFF0FDF4" } };
  headerRow.fill = { type: "pattern", pattern: "solid", fgColor: { argb: "FF166534" } };
  headerRow.alignment = { horizontal: "left", vertical: "middle" };

  for (var i = 1; i < metaRows.length; i++) {
    ws.addRow(metaRows[i]);
  }

  ws.getColumn(1).width = 24;
  ws.getColumn(2).width = 34;
  ws.views = [{ state: "frozen", ySplit: 3 }];
}

function appendTreeSelectionMetaSheetSheetJS(wb) {
  if (!wb) return;

  var ws = XLSX.utils.aoa_to_sheet(getTreeSelectionExportMetaRows());
  XLSX.utils.book_append_sheet(wb, ws, "Metadatos");
}

function getFirstNodeByLocalName(root, name) {
  if (!root) return null;
  var nodes = findAllByLocalName(root, name);
  return nodes && nodes.length ? nodes[0] : null;
}

function updateHeaderMetaInfo(xmlDoc) {
  var ieds = xmlDoc ? findAllByLocalName(xmlDoc, "IED") : [];
  var header = getFirstNodeByLocalName(xmlDoc, "Header");
  var scl = xmlDoc && xmlDoc.documentElement ? xmlDoc.documentElement : null;

  function getIedMetaValue(iedNode, attrName) {
    return iedNode && iedNode.getAttribute ? (iedNode.getAttribute(attrName) || "") : "";
  }

  function isCompleteIed(iedNode) {
    return Boolean(
      getIedMetaValue(iedNode, "name") &&
      getIedMetaValue(iedNode, "type") &&
      getIedMetaValue(iedNode, "manufacturer") &&
      (getIedMetaValue(iedNode, "configVersion") || getIedMetaValue(iedNode, "revision") || getIedMetaValue(iedNode, "version"))
    );
  }

  var ied = null;
  for (var i = 0; i < ieds.length; i++) {
    if (isCompleteIed(ieds[i])) {
      ied = ieds[i];
      break;
    }
  }
  if (!ied && ieds.length) ied = ieds[0];

  var metaName = getIedMetaValue(ied, "name") || "—";
  var metaType = getIedMetaValue(ied, "type") || "";
  var metaManufacturer = getIedMetaValue(ied, "manufacturer") || "";
  var metaVersion = "";
  for (var i = 0; i < ieds.length; i++) {
    var candidateIed = ieds[i];
    if (candidateIed && candidateIed.getAttribute) {
      metaVersion = candidateIed.getAttribute("configVersion") || candidateIed.getAttribute("revision") || candidateIed.getAttribute("version") || "";
      if (metaVersion) break;
    }
  }

  if (!metaType && scl && scl.getAttribute) metaType = scl.getAttribute("nameStructure") || "";
  if (!metaVersion && header && header.getAttribute) {
    metaVersion = header.getAttribute("version") || header.getAttribute("revision") || "";
  }

  setHeaderMetaValue("meta-name", metaName);
  setHeaderMetaValue("meta-type", metaType);
  setHeaderMetaValue("meta-manufacturer", metaManufacturer);
  setHeaderMetaValue("meta-config-version", metaVersion);
}

function resetHeaderMetaInfo() {
  setHeaderMetaValue("meta-name", "—");
  setHeaderMetaValue("meta-type", "");
  setHeaderMetaValue("meta-manufacturer", "");
  setHeaderMetaValue("meta-config-version", "");
}
function parseXml(text) {
  try {
    setStatus("Analizando archivo...");
    var parser = new DOMParser();
    var xmlDoc = parser.parseFromString(text, "text/xml");
    if (xmlDoc.getElementsByTagName("parsererror").length) {
      setStatus("Error: XML no válido.");
      return;
    }

    flatNodes = [];
    lnRecords = [];
    treeSelectedNodes = {};
    datasetSelectedRecords = {};
    datasetSelectedOrder = [];
    buildDataModelIndex(xmlDoc);
    updateHeaderMetaInfo(xmlDoc);

    var root = xmlDoc.documentElement;
    var treeData = [];
    if (root && root.children && root.children.length === 0 && hasAttrs(root)) {
      var rootNode = buildTreeNode(root, 0, {});
      if (rootNode) treeData.push(rootNode);
    } else {
      for (var i = 0; i < root.children.length; i++) {
        var node = buildTreeNode(root.children[i], 0, {});
        if (node) treeData.push(node);
      }
    }

    renderTree(treeData);
    refreshLNodeTypeDoCidAttributes();
    renderDatasetTable(lnRecords);
    populateDatasetFilters();
    renderDatasetSheet();

    if (!treeData.length) {
      setStatus(
        "Archivo leído, pero no se generó un árbol. Comprueba que el archivo sea CID/SCL válido.",
      );
    } else {
      setStatus("Archivo cargado. " + lnRecords.length + " registros encontrados.");
    }
  } catch (ex) {
    setStatus("Error: " + ex.message);
    console.error(ex);
  }
}

function bindFileInput() {
  var fileInput = document.getElementById("fileInput");
  if (!fileInput || fileInput.dataset.bound === "1") return;
  fileInput.dataset.bound = "1";
  fileInput.addEventListener("change", function (e) {
    var file = e.target.files[0];
    if (!file) {
      resetHeaderMetaInfo();
      return;
    }
    setStatus("Leyendo archivo: " + file.name + "...");
    var reader = new FileReader();
    reader.onload = function () {
      var buffer = reader.result;
      var text = "";

      function decodeWith(encoding) {
        try {
          if (typeof TextDecoder !== "undefined") {
            return new TextDecoder(encoding).decode(new Uint8Array(buffer));
          }
        } catch (err) {
          return null;
        }
        return null;
      }

      if (buffer && buffer.byteLength >= 2) {
        var view = new Uint8Array(buffer);
        if (view[0] === 0xFF && view[1] === 0xFE) {
          text = decodeWith("utf-16le") || "";
        } else if (view[0] === 0xFE && view[1] === 0xFF) {
          text = decodeWith("utf-16be") || "";
        } else {
          text = decodeWith("utf-8") || "";
          if (text.indexOf("\u0000") !== -1) {
            var utf16leText = decodeWith("utf-16le") || "";
            var utf16beText = decodeWith("utf-16be") || "";
            text = utf16leText.length > utf16beText.length ? utf16leText : utf16beText;
          }
        }
      } else if (buffer) {
        text = decodeWith("utf-8") || "";
      }

      if (text) text = text.replace(/^\uFEFF/, "");
      if (!text) {
        setStatus("Error: no se pudo decodificar el archivo.");
        return;
      }
      parseXml(text);
    };
    reader.onerror = function () {
      setStatus("Error: no se pudo leer el archivo.");
    };
    reader.readAsArrayBuffer(file);
  });
}

if (document.readyState === "loading") {
  document.addEventListener("DOMContentLoaded", bindFileInput);
} else {
  bindFileInput();
}

// Funciones para manejar checkboxes y descargas seleccionadas
function toggleAllRows() {
  var chkAll = document.getElementById("chk-all-rows");
  var checkboxes = document.querySelectorAll(".row-checkbox");
  checkboxes.forEach(function (chk) {
    chk.checked = chkAll.checked;
  });
  if (chkAll.checked) {
    datasetSelectedOrder = [];
    checkboxes.forEach(function (chk) {
      var idx = parseInt(chk.dataset.index, 10);
      if (!isNaN(idx) && idx >= 0 && idx < lnRecords.length) {
        var rec = lnRecords[idx];
        var key = createDatasetKey(idx, rec);
        if (datasetSelectedOrder.indexOf(key) === -1) datasetSelectedOrder.push(key);
      }
    });
  } else {
    datasetSelectedOrder = [];
  }
  updateSelectedCount();
}

function updateSelectedCount() {
  var checkboxes = document.querySelectorAll(".row-checkbox");
  var count = 0;
  checkboxes.forEach(function (chk) {
    if (chk.checked) count++;
  });
  var countEl = document.getElementById("selected-count");
  if (countEl) {
    countEl.textContent = count + " " + (count === 1 ? "seleccionado" : "seleccionados");
  }
  
  // Actualizar estado del checkbox "seleccionar todo"
  var chkAll = document.getElementById("chk-all-rows");
  if (chkAll) {
    chkAll.checked = count > 0 && count === checkboxes.length;
  }
  updateDatasetSelectionDisplay();
  if (count > 0) {
    setStatus("Se actualizaron los registros seleccionados del dataset.");
  }
}

function onRowCheckboxChange(chk) {
  var idx = parseInt(chk.dataset.index, 10);
  if (isNaN(idx) || idx < 0 || idx >= lnRecords.length) return;
  var rec = lnRecords[idx];
  var key = createDatasetKey(idx, rec);
  if (chk.checked) {
    datasetSelectedRecords[key] = rec;
    if (datasetSelectedOrder.indexOf(key) === -1) datasetSelectedOrder.push(key);
    var tr = chk.closest('tr');
    if (tr) tr.classList.add('row-selected');

    // Auto-populate tree selection when FCDA is selected and DOName matches lnClass from LNodeType
    if (rec.Tag === "FCDA" && rec.DOName && rec["LNodeType (CID)"]) {
      var lnodeType = lnodeTypeIndex[rec["LNodeType (CID)"]];
      if (lnodeType && lnodeType.lnClass) {
        // Check if lnClass from LNodeType matches DOName of FCDA
        if (normalizeName(lnodeType.lnClass) === normalizeName(rec.DOName)) {
          // Create a tree node entry with LDIns, Prefix, and LnInst populated
          var nodeId = "fcda_auto_" + key;
          var treeNodeData = {
            text: "FCDA " + (rec.DOName || "") + " · " + (rec.DAName || ""),
            tag: "FCDA",
            attrs: {
              ldInst: rec.LDInst || "",
              prefix: rec.Prefix || "",
              lnClass: rec.LNClass || "",
              lnInst: rec.LNInst || "",
              lnType: rec["LNodeType (CID)"] || "",
              doName: rec.DOName || "",
              daName: rec.DAName || "",
              fc: rec.fc || ""
            },
            ctx: {
              iedName: rec.IED || "",
              ldInst: rec.LDInst || "",
              prefix: rec.Prefix || "",
              lnClass: rec.LNClass || "",
              lnInst: rec.LNInst || ""
            },
            label: rec.IED + " > " + rec.LNClass + " > " + rec.DOName
          };
          treeSelectedNodes[nodeId] = treeNodeData;
          if (treeSelectedOrder.indexOf(nodeId) === -1) {
            treeSelectedOrder.push(nodeId);
          }
          if (typeof scheduleUpdateTreeSelectionDisplay === 'function') {
            scheduleUpdateTreeSelectionDisplay();
          } else {
            updateTreeSelectionDisplay();
          }
        }
      }
    }
  } else {
    if (datasetSelectedRecords[key]) delete datasetSelectedRecords[key];
    var p = datasetSelectedOrder.indexOf(key);
    if (p !== -1) datasetSelectedOrder.splice(p, 1);
    var tr = chk.closest('tr');
    if (tr) tr.classList.remove('row-selected');

    // Remove auto-generated tree node when FCDA is deselected
    var nodeId = "fcda_auto_" + key;
    if (treeSelectedNodes[nodeId]) {
      delete treeSelectedNodes[nodeId];
      var orderIdx = treeSelectedOrder.indexOf(nodeId);
      if (orderIdx !== -1) {
        treeSelectedOrder.splice(orderIdx, 1);
      }
      if (typeof scheduleUpdateTreeSelectionDisplay === 'function') {
        scheduleUpdateTreeSelectionDisplay();
      } else {
        updateTreeSelectionDisplay();
      }
    }
  }
  updateSelectedCount();
}

function updateDatasetSelectionDisplay() {
  var listDiv = document.getElementById("dataset-selected-list");
  if (!listDiv) return;
  
  var tbody = document.getElementById("ds-tbody");
  if (!tbody) return;
  
  var checkboxes = tbody.querySelectorAll(".row-checkbox");
  var newSelected = {};
  checkboxes.forEach(function (chk) {
    if (chk.checked) {
      var idx = parseInt(chk.dataset.index, 10);
      if (!isNaN(idx) && idx >= 0 && idx < lnRecords.length) {
        var record = lnRecords[idx];
        var key = createDatasetKey(idx, record);
        newSelected[key] = record;
      }
    }
  });

  datasetSelectedRecords = newSelected;

  // Keep selection order: remove keys no longer present, append any new keys
  datasetSelectedOrder = datasetSelectedOrder.filter(function (k) {
    return datasetSelectedRecords[k];
  });
  Object.keys(datasetSelectedRecords).forEach(function (k) {
    if (datasetSelectedOrder.indexOf(k) === -1) datasetSelectedOrder.push(k);
  });

  var selectedKeys = datasetSelectedOrder.slice();
  if (selectedKeys.length === 0) {
    listDiv.innerHTML = '<div style="color: #64748b; text-align: center; padding: 20px;">Selecciona registros en el Dataset para verlos aquí</div>';
    return;
  }

  var headerHtml = '';
  headerHtml += '<div style="display:flex;justify-content:space-between;align-items:center;gap:10px;padding:8px 8px 10px;border-bottom:1px solid #1e3a2f;margin-bottom:8px;">';
  headerHtml += '<span style="color:#cbd5e1;font-size:11px;font-weight:700;letter-spacing:0.03em;">Seleccionados: ' + selectedKeys.length + '</span>';
  headerHtml += '<button type="button" onclick="clearAllDatasetSelections()" style="background:#b91c1c;border:none;color:white;padding:5px 10px;border-radius:6px;cursor:pointer;font-size:11px;font-weight:700;flex-shrink:0;">Eliminar todo</button>';
  headerHtml += '</div>';

  var html = "";
  selectedKeys.forEach(function (key) {
    var record = datasetSelectedRecords[key];
    if (!record) return;
    var displayText = (record.IED || "") + " > " + (record.LNClass || "") + " > " + (record.DOName || "");
    html += '<div style="padding: 6px; border-bottom: 1px solid #1e3a2f; display: flex; justify-content: space-between; align-items: center; font-size: 11px;">';
    html += '<span style="color: #e2e8f0; flex: 1; white-space: nowrap; overflow: hidden; text-overflow: ellipsis;" title="' + displayText + '">' + displayText + '</span>';
    html += '<button type="button" class="dataset-row-remove" data-key="' + esc(encodeURIComponent(key)) + '" style="background: linear-gradient(180deg, #ef4444 0%, #b91c1c 100%); border: 1px solid #fca5a5; color: white; padding: 2px 6px; border-radius: 3px; cursor: pointer; font-size: 10px; margin-left: 4px; flex-shrink: 0; box-shadow: 0 4px 10px rgba(153, 27, 27, 0.28);">✕</button>';
    html += '</div>';
  });
  listDiv.innerHTML = headerHtml + html;

  var removeButtons = listDiv.querySelectorAll(".dataset-row-remove");
  removeButtons.forEach(function (btn) {
    btn.addEventListener("click", function (e) {
      e.preventDefault();
      e.stopPropagation();
      var key = btn.getAttribute("data-key") || "";
      removeDatasetSelection(decodeURIComponent(key));
    });
  });
}

function clearAllDatasetSelections() {
  var keys = datasetSelectedOrder.slice();
  var tbody = document.getElementById("ds-tbody");

  keys.forEach(function (key) {
    var nodeId = "fcda_auto_" + key;
    if (treeSelectedNodes[nodeId]) {
      delete treeSelectedNodes[nodeId];
      var nodeOrderIdx = treeSelectedOrder.indexOf(nodeId);
      if (nodeOrderIdx !== -1) treeSelectedOrder.splice(nodeOrderIdx, 1);
    }
  });

  datasetSelectedRecords = {};
  datasetSelectedOrder = [];

  if (tbody) {
    tbody.querySelectorAll(".row-checkbox").forEach(function (chk) {
      chk.checked = false;
      var tr = chk.closest("tr");
      if (tr) tr.classList.remove("row-selected");
    });
  }

  var chkAll = document.getElementById("chk-all-rows");
  if (chkAll) chkAll.checked = false;

  updateDatasetSelectionDisplay();
  updateTreeSelectionDisplay();
  updateSelectedCount();
  setStatus("Se eliminaron todas las filas seleccionadas del dataset.");
}

function removeDatasetSelection(key) {
  if (!key || !datasetSelectedRecords[key]) return;

  delete datasetSelectedRecords[key];

  var tbody = document.getElementById("ds-tbody");
  if (tbody) {
    var checkboxes = tbody.querySelectorAll(".row-checkbox");
    checkboxes.forEach(function (chk) {
      var idx = parseInt(chk.dataset.index, 10);
      if (isNaN(idx) || idx < 0 || idx >= lnRecords.length) return;
      var rec = lnRecords[idx];
      var chkKey = createDatasetKey(idx, rec);
      if (chkKey === key) {
        chk.checked = false;
      }
    });
  }

  var p = datasetSelectedOrder.indexOf(key);
  if (p !== -1) datasetSelectedOrder.splice(p, 1);
  updateSelectedCount();
}

function getSelectedRecords() {
  var selected = [];
  datasetSelectedOrder.forEach(function (key) {
    if (datasetSelectedRecords[key]) selected.push(datasetSelectedRecords[key]);
  });
  return selected;
}

function exportSelectedDataset() {
  var selected = getSelectedRecords();
  if (!selected.length) {
    alert("Selecciona al menos una fila para descargar.");
    return;
  }
  
  setStatus("Generando descarga de datos seleccionados...");
  if (typeof ExcelJS === "undefined" || !ExcelJS.Workbook) {
    setStatus("ExcelJS no disponible: exportando datos seleccionados con formato básico...");
    return exportSelectedDatasetFallback(selected);
  }
  try {
    var workbook = new ExcelJS.Workbook();
    workbook.creator = "CID Tool";
    workbook.created = new Date();
    var ws = workbook.addWorksheet("Dataset Seleccionado");

    ws.mergeCells("A1:S1");
    ws.getCell("A1").value = "CID Dataset - Datos Seleccionados";
    ws.getCell("A1").font = { size: 14, bold: true, color: { argb: "FFFFFFFF" } };
    ws.getCell("A1").alignment = { horizontal: "center", vertical: "middle" };
    ws.getRow(1).height = 28;

    ws.mergeCells("A2:S2");
    ws.getCell("A2").value = "Generado: " + new Date().toLocaleString() + " | Total: " + selected.length + " registros";
    ws.getCell("A2").font = {
      size: 10,
      italic: true,
      color: { argb: "FFCCCCCC" },
    };
    ws.getCell("A2").alignment = { horizontal: "right", vertical: "middle" };

    var headers = [
      "IED",
      "DataSet",
      "LDIns",
      "Prefix",
      "LNClass",
      "LNInst",
      "lnClass (CID)",
      "DOName",
      "DAType",
      "CDC",
      "DAName",
      "Tag",
      "CONCAT",
    ];

    ws.addRow([]);
    var headerRow = ws.addRow(headers);
    headerRow.font = { bold: true, color: { argb: "FFFFFFFF" }, size: 11 };
    headerRow.fill = {
      type: "pattern",
      pattern: "solid",
      fgColor: { argb: "FF059669" },
    };
    headerRow.alignment = { horizontal: "center", vertical: "middle", wrapText: true };
    ws.getRow(3).height = 20;

    selected.forEach(function (r) {
      ws.addRow([
        r.IED,
        r.DataSet || "",
        r.LDInst,
        r.Prefix,
        r.LNClass,
        r.LNInst,
        r.lnClassCID || "",
        r.DOName,
        r.DAType || "",
        r.CDC || "",
        r.DAName || "",
        r.Tag,
        r.CONCAT || "",
      ]);
    });

    applyExcelAutoFit(ws, 12);
    ws.views = [{ state: "frozen", xSplit: 0, ySplit: 3 }];

    workbook.xlsx.writeBuffer().then(function (buffer) {
      saveBlobAs(new Blob([buffer], { type: "application/octet-stream" }), "CID_Dataset_Seleccionado.xlsx");
      setStatus("✓ Descarga completada. " + selected.length + " registros exportados.");
    });
  } catch (ex) {
    setStatus("Error: " + ex.message);
    console.error(ex);
  }
}

function exportSelectedDatasetFallback(selected) {
  var rows = [];
  rows.push(["CID Dataset - Datos Seleccionados"]);
  rows.push(["Generado:", new Date().toLocaleString(), "Total:", selected.length + " registros"]);
  rows.push([]);
  rows.push([
    "IED",
    "DataSet",
    "LDInst",
    "Prefix",
    "LNClass",
    "LNInst",
    "lnClass (CID)",
    "DOName",
    "DAType",
    "CDC",
    "DAName",
    "Tag",
    "CONCAT",
  ]);

  selected.forEach(function (r) {
    rows.push([
      r.IED,
      r.DataSet || "",
      r.LDInst,
      r.Prefix,
      r.LNClass,
      r.LNInst,
      r.lnClassCID || "",
      r.DOName,
      r.DAType || "",
      r.CDC || "",
      r.DAName || "",
      r.Tag,
      r.CONCAT || "",
    ]);
  });

  exportWithSheetJS("CID_Dataset_Seleccionado.xlsx", rows, "Dataset Seleccionado");
  setStatus("✓ Descarga completada. " + selected.length + " registros exportados.");
}

// Funciones para manejar checkboxes del árbol
function toggleTreeNodeSelection(nodeId, nodeData) {
  var existed = Boolean(treeSelectedNodes[nodeId]);
  if (existed) {
    delete treeSelectedNodes[nodeId];
  } else if (nodeData) {
    treeSelectedNodes[nodeId] = nodeData;
  }

  var orderIndex = treeSelectedOrder.indexOf(nodeId);
  if (orderIndex !== -1) {
    treeSelectedOrder.splice(orderIndex, 1);
  }

  var tree = window._cachedJstree || (window._cachedJstree = (window.jQuery && window.jQuery("#jstree").length ? window.jQuery("#jstree").jstree(true) : null));
  if (tree && typeof tree.uncheck_node === "function") {
    try {
      tree.uncheck_node(nodeId);
    } catch (e) {
      console.warn("No se pudo desmarcar el nodo del árbol", e);
    }
  }

  if (typeof scheduleUpdateTreeSelectionDisplay === 'function') {
    scheduleUpdateTreeSelectionDisplay();
  } else {
    updateTreeSelectionDisplay();
  }
  if (Object.keys(treeSelectedNodes).length > 0) {
    setStatus("Se actualizaron los elementos seleccionados del árbol.");
  }
}

function getTreeNodeDisplayFields(node) {
  var attrs = node && node.attrs ? node.attrs : {};
  var readableText = stripVisibleTypePrefixes(getReadableNodeLabel(node));
  var readableValue = stripVisibleTypePrefixes(attrs.value || attrs.text || attrs.Val || attrs.val || "");
  return {
    text: readableText,
    tag: node.tag || "",
    type: attrs.type || attrs.Type || "",
    lnodeTypeCID: attrs["lnType (CID)"] || attrs.lnType || "",
    lnClassCID: attrs["lnClass (CID)"] || attrs.lnClass || "",
    subclasses: attrs.subclasses || attrs.Subclasses ||
      (attrs.type && daTypeIndex[attrs.type] && daTypeIndex[attrs.type].bdas ? daTypeIndex[attrs.type].bdas.length + " subclases" : "") ||
      (attrs.id && doTypeIndex[attrs.id] && doTypeIndex[attrs.id].das ? doTypeIndex[attrs.id].das.length + " subclases" : "") ||
      (node.children && node.children.length ? node.children.length + " subclases" : ""),
    desc: attrs.desc || attrs.Desc || attrs.description || attrs.Description || "",
    val: readableValue,
    dataAttr: readableValue || attrs.daName || attrs.DAName || attrs.name || "",
  };
}

function getSelectedTreeIds() {
  var ids = [];
  var orderIds = Array.isArray(treeSelectedOrder) ? treeSelectedOrder.slice() : [];
  var objectIds = Object.keys(treeSelectedNodes || {});

  orderIds.forEach(function (id) {
    if (id && objectIds.indexOf(String(id)) !== -1 && ids.indexOf(String(id)) === -1) ids.push(String(id));
  });
  objectIds.forEach(function (id) {
    if (ids.indexOf(String(id)) === -1) ids.push(String(id));
  });

  return ids;
}

function getTreeNodeOrderPath(nodeId) {
  var tree = window._cachedJstree || (window._cachedJstree = (window.jQuery && window.jQuery("#jstree").length ? window.jQuery("#jstree").jstree(true) : null));
  if (!tree || !nodeId) return null;

  var node = tree.get_node(nodeId);
  if (!node || !node.id) return null;

  var path = [];
  var current = node;

  while (current && current.id && current.id !== "#") {
    var parent = current.parent ? tree.get_node(current.parent) : null;
    var siblings = parent && Array.isArray(parent.children) ? parent.children : (tree._model && tree._model.data["#"] ? tree._model.data["#"].children || [] : []);
    var index = siblings.indexOf(current.id);
    path.unshift(index === -1 ? 999999 : index);
    current = parent;
  }

  return path;
}

function compareTreeOrderPaths(pathA, pathB) {
  if (!pathA && !pathB) return 0;
  if (!pathA) return 1;
  if (!pathB) return -1;

  var length = Math.max(pathA.length, pathB.length);
  for (var i = 0; i < length; i++) {
    var a = typeof pathA[i] === "number" ? pathA[i] : -1;
    var b = typeof pathB[i] === "number" ? pathB[i] : -1;
    if (a !== b) return a - b;
  }
  return 0;
}

function sortTreeSelectedIds(selectedIds) {
  return (selectedIds || []).slice().sort(function (a, b) {
    var treeOrder = compareTreeOrderPaths(getTreeNodeOrderPath(a), getTreeNodeOrderPath(b));
    if (treeOrder !== 0) return treeOrder;

    var na = treeSelectedNodes[a] || {};
    var nb = treeSelectedNodes[b] || {};
    var fa = getTreeNodeDisplayFields(na);
    var fb = getTreeNodeDisplayFields(nb);
    var typeA = (fa.type || "").toLowerCase();
    var typeB = (fb.type || "").toLowerCase();
    if (typeA !== typeB) return typeA.localeCompare(typeB);
    return (fa.text || "").localeCompare(fb.text || "");
  });
}

function buildCadenaPreviewEntries(selectedIds) {
  var entries = [];
  var seenEntryKeys = {};
  var seenRowKeys = {};
  var seenUniqueIdentifiers = {};
  var consumedExcludedKeys = {};
  var pendingItems = [];

  (selectedIds || []).forEach(function (id) {
    var node = treeSelectedNodes[id] || {};
    var rows = [];
    collectCadenaRowsFromTreeNode(node, id, rows);
    rows.forEach(function (row) {
      if (isStructBType(row[row.length - 3] || "")) return;
      pendingItems.push({ id: id, node: node, row: row });
    });
  });

  var maxPathCount = getCadenaMaxPathCountFromRows(pendingItems.map(function (item) { return item.row; }));

  pendingItems.forEach(function (item) {
    var id = item.id;
    var node = item.node;
    var row = item.row;
    var normalizedRow = limitCadenaPathColumns(row, maxPathCount);
    var bType = normalizedRow[normalizedRow.length - 3] || "";
    var rowKey = cadenaRowKey(normalizedRow);
    var entryKey = id + "||" + rowKey;

    var allowDuplicateRowsForNode = false;
    var nodeTagUpper = String((node && node.tag) || "").toUpperCase();
    if (
      nodeTagUpper === "BDA" || nodeTagUpper === "BDA_SYNTH" || nodeTagUpper === "BDA_CONTENT" ||
      nodeTagUpper === "SDO" || nodeTagUpper === "SDO_SYNTH"
    ) {
      allowDuplicateRowsForNode = true;
    }

    var uniqueIdentifier = [
      normalizedRow[1] || "", normalizedRow[2] || "", normalizedRow[3] || "", normalizedRow[4] || "",
      normalizedRow[5] || "", normalizedRow[6] || "", normalizedRow[7] || "", bType || "",
      normalizedRow[normalizedRow.length - 2] || ""
    ].join("||");

    var excludedCount = typeof getCadenaExcludedRowCount === 'function' ? getCadenaExcludedRowCount(entryKey) : (cadenaExcludedRowKeys[entryKey] ? 1 : 0);
    var consumedCount = consumedExcludedKeys[entryKey] || 0;
    if (consumedCount < excludedCount) {
      consumedExcludedKeys[entryKey] = consumedCount + 1;
      return;
    }

    if (seenEntryKeys[entryKey]) return;
    if (!allowDuplicateRowsForNode) {
      if (seenRowKeys[rowKey] || seenUniqueIdentifiers[uniqueIdentifier]) return;
      seenRowKeys[rowKey] = true;
      seenUniqueIdentifiers[uniqueIdentifier] = true;
    }

    seenEntryKeys[entryKey] = true;
    entries.push({ row: row, nodeId: id, node: node, matched: false, key: entryKey, rowKey: rowKey });
  });

  return entries;
}

function pruneCadenaExcludedRows(selectedIds) {
  var activeKeys = {};
  var activeRowKeys = {};

  (selectedIds || []).forEach(function (id) {
    var node = treeSelectedNodes[id] || {};
    var rows = [];
    collectCadenaRowsFromTreeNode(node, id, rows);
    rows.forEach(function (row) {
      var key = id + "||" + cadenaRowKey(row);
      var rowKey = cadenaRowKey(row);
      if (key) activeKeys[key] = true;
      if (rowKey) activeRowKeys[rowKey] = true;
    });
  });

  Object.keys(cadenaExcludedRowKeys || {}).forEach(function (key) {
    if (!activeKeys[key] && !activeRowKeys[key]) {
      delete cadenaExcludedRowKeys[key];
    }
  });
}

// Inversa de excludeCadenaRowsForTreeNode: cuando un nodo se vuelve a marcar
// (checkbox) en el árbol, se limpian las exclusiones (tanto la específica del
// nodo como la global de contenido) que pudieran haber quedado registradas
// por una eliminación manual previa desde la tabla (botón ✕ de la fila) o por
// un desmarcado anterior. Así, volver a seleccionar un elemento eliminado
// hace que su fila reaparezca de inmediato en "Elementos Seleccionados del Árbol".
function clearCadenaExclusionsForNode(node) {
  if (!node || !node.original || !node.original._meta) return;

  var tree = window._cachedJstree || (window._cachedJstree = (window.jQuery && window.jQuery("#jstree").length ? window.jQuery("#jstree").jstree(true) : null));
  var parentIds = Array.isArray(node.parents) ? node.parents.filter(function (pid) { return pid && pid !== "#"; }) : [];
  var parentPath = parentIds.map(function (pid) {
    var parent = tree ? tree.get_node(pid) : null;
    return parent && parent.text ? parent.text : "";
  }).filter(Boolean).concat([node.text]).join(" / ");

  var storedNode = enrichStoredTreeNode(
    {
      text: node.text,
      tag: node.original._meta.tag || "",
      attrs: Object.assign({}, node.original._meta.attrs || {}),
      ctx: Object.assign({}, node.original._meta.ctx || {}),
      label: node.text,
      parentIds: parentIds,
      parentPath: parentPath,
    },
    node.id
  );

  var rows = [];
  collectCadenaRowsFromTreeNode(storedNode, node.id, rows);
  if (typeof clearCadenaPreviewRemovedRowsForNode === 'function') {
    clearCadenaPreviewRemovedRowsForNode(node.id, rows);
  }
  if (typeof clearCadenaPreviewHiddenEntriesForNode === 'function') {
    clearCadenaPreviewHiddenEntriesForNode(node.id, rows);
  }
  rows.forEach(function (row) {
    var rowKey = cadenaRowKey(row);
    if (!rowKey) return;
    if (typeof clearCadenaExcludedRowCount === 'function') {
      clearCadenaExcludedRowCount(node.id + "||" + rowKey);
      clearCadenaExcludedRowCount(rowKey);
    }
    delete cadenaExcludedRowKeys[node.id + "||" + rowKey];
    delete cadenaExcludedRowKeys[rowKey];
  });

  if (typeof clearCadenaEntriesCache === 'function') {
    clearCadenaEntriesCache();
  }
}

function excludeCadenaRowsForTreeNode(tree, node) {
  if (!tree || !node || !node.original || !node.original._meta) return;

  var parentIds = Array.isArray(node.parents) ? node.parents.filter(function (pid) { return pid && pid !== "#"; }) : [];
  var parentPath = parentIds.map(function (pid) {
    var parent = tree.get_node(pid);
    return parent && parent.text ? parent.text : "";
  }).filter(Boolean).concat([node.text]).join(" / ");

  var storedNode = enrichStoredTreeNode(
    {
      text: node.text,
      tag: node.original._meta.tag || "",
      attrs: Object.assign({}, node.original._meta.attrs || {}),
      ctx: Object.assign({}, node.original._meta.ctx || {}),
      label: node.text,
      parentIds: parentIds,
      parentPath: parentPath,
    },
    node.id
  );

  var rows = [];
  collectCadenaRowsFromTreeNode(storedNode, node.id, rows);
  rows.forEach(function (row) {
    var rowKey = cadenaRowKey(row);
    if (!rowKey) return;
    incrementCadenaExcludedRowCount(node.id + "||" + rowKey);
  });
}

function getCadenaPreviewResult(row) {
  if (!Array.isArray(row) || !row.length) return "";
  var result = String(row[row.length - 1] || "").trim();
  if (result) return result;

  var ldInst = row[1] || "";
  var prefix = row[2] || "";
  var lnClass = row[3] || "";
  var lnInst = row[4] || "";
  var doName = row[5] || "";
  var sdoName = row[6] || "";
  var pathParts = [];

  for (var i = 7; i < row.length - 3; i++) {
    if (row[i] !== undefined && row[i] !== null && String(row[i]).trim() !== "") {
      pathParts.push(String(row[i]));
    }
  }

  var root = String(ldInst || "") + "." + String(prefix || "") + String(lnClass || "") + String(lnInst || "");
  var parts = [];
  if (doName) parts.push(doName);
  if (sdoName) parts.push(sdoName);
  parts = parts.concat(pathParts);
  return root + (parts.length ? "." + parts.join(".") : "");
}

function getPreviewLnType(entry) {
  var node = entry && entry.node ? entry.node : {};
  var attrs = node.attrs || {};
  var ctx = node.ctx || {};
  if (attrs.id && String(node.tag || "").toUpperCase() === "LNODETYPE") return attrs.id;
  if (attrs["lnType (CID)"] || attrs.lnType || ctx.lnType) return attrs["lnType (CID)"] || attrs.lnType || ctx.lnType;

  var row = entry && Array.isArray(entry.row) ? entry.row : [];
  var ldInst = row[1] || "";
  var prefix = row[2] || "";
  var lnClass = row[3] || "";
  var lnInst = row[4] || "";

  for (var i = 0; i < lnRecords.length; i++) {
    var rec = lnRecords[i] || {};
    var sameLdInst = !!(ldInst && rec.LDInst && isSameValue(rec.LDInst, ldInst));
    if (ldInst && rec.LDInst && !sameLdInst) continue;
    if (!sameLdInst && prefix && rec.Prefix && normalizeName(rec.Prefix) !== normalizeName(prefix)) continue;
    if (!sameLdInst && lnClass && rec.LNClass && normalizeName(rec.LNClass) !== normalizeName(lnClass)) continue;
    if (!sameLdInst && lnInst && rec.LNInst && normalizeName(rec.LNInst) !== normalizeName(lnInst)) continue;
    if (rec.LNodeType) return rec.LNodeType;
  }

  return "";
}

function getPreviewDoDescription(entry) {
  var row = entry && Array.isArray(entry.row) ? entry.row : [];
  var doName = row[5] || "";
  if (!doName) return "";

  var node = entry && entry.node ? entry.node : {};
  var attrs = node.attrs || {};
  var directDesc = attrs.doDesc || attrs.DODesc || attrs["DO desc"] || "";
  var sourceDoName = normalizeName(attrs.doName || attrs.DOName || attrs.name || "");
  if (directDesc && sourceDoName && normalizeName(doName) === sourceDoName) return directDesc;

  var fields = {
    ldInst: row[1] || "",
    prefix: row[2] || "",
    lnClass: row[3] || "",
    lnInst: row[4] || "",
    doName: doName,
    lnType: getPreviewLnType(entry),
  };
  var doiDesc = getDoiDescriptionForContext(doName, fields, attrs, node.ctx || {});
  if (doiDesc) return doiDesc;
  return getCidDescriptionFields(fields, attrs, node.ctx || {}).doDesc || "";
}

function getCadenaPreviewDescription(entry) {
  var node = entry && entry.node ? entry.node : {};
  var attrs = node.attrs || {};
  var ctx = node.ctx || {};
  var ldDesc = ctx.ldDesc || attrs.ldDesc || "";
  var lnDesc = ctx.lnDesc || ctx.desc || attrs.lnDesc || "";
  var doDesc = getPreviewDoDescription(entry);
  return buildCompositeDescription(ldDesc, lnDesc, doDesc);
}

function getCadenaDescriptionFields(entry) {
  var node = entry && entry.node ? entry.node : {};
  var attrs = node.attrs || {};
  var ctx = node.ctx || {};
  var row = entry && Array.isArray(entry.row) ? entry.row : [];
  var cidDesc = getCidDescriptionFields({
    ldInst: row[1] || "",
    prefix: row[2] || "",
    lnClass: row[3] || "",
    lnInst: row[4] || "",
    doName: row[5] || "",
    lnType: getPreviewLnType(entry),
  }, attrs, ctx);
  return {
    ldDesc: cidDesc.ldDesc || "",
    lnDesc: cidDesc.lnDesc || "",
    doDesc: cidDesc.doDesc || "",
  };
}

function renderCadenaPreviewTable(entries) {
  var maxPathCount = Math.max(3, getCadenaMaxPathCountFromRows((entries || []).map(function (entry) {
    return entry && entry.row ? entry.row : [];
  })));

  function getDisplaySdoName(value) {
    var text = String(value || "").trim();
    if (!text) return "";
    var parts = text.split(".").filter(function (part) { return part; });
    return parts.length ? parts[parts.length - 1] : text;
  }

  var html = '<div class="cadena-preview-wrap"><table class="cadena-preview-table"><thead>';
  html += '<tr class="cadena-head-row">';
  html += '<th rowspan="2" class="cadena-th-ld">LDIns</th>';
  html += '<th colspan="3" class="cadena-th-ln">LN</th>';
  html += '<th colspan="2" class="cadena-th-do">DO</th>';
  html += '<th colspan="' + maxPathCount + '" class="cadena-th-da">DA</th>';
  html += '<th rowspan="2" class="cadena-th-da">bType</th>';
  html += '<th rowspan="2" class="cadena-th-da">FC</th>';
  html += '<th rowspan="2" class="cadena-th-result">CADENA IEC 61850</th>';
  html += '<th colspan="3" class="cadena-th-result">DESCRIPCION</th>';
  html += '<th rowspan="2" class="cadena-th-action" title="Eliminar todos los elementos seleccionados"><button type="button" class="cadena-row-remove cadena-row-remove-all" onclick="clearAllTreeSelection()" aria-label="Eliminar todos los elementos seleccionados"><i class="fa-solid fa-xmark" aria-hidden="true"></i></button></th>';
  html += "</tr>";
  html += '<tr class="cadena-head-row cadena-head-row-sub">';
  html += '<th class="cadena-th-ln">Prefix</th>';
  html += '<th class="cadena-th-ln">LNClass</th>';
  html += '<th class="cadena-th-ln">LNInst</th>';
  html += '<th class="cadena-th-do">DO</th>';
  html += '<th class="cadena-th-do">SDO</th>';
  for (var pi = 0; pi < maxPathCount; pi++) {
    var label = pi === 0 ? "DA" : (pi === 1 ? "BDA" : "BDA" + pi);
    html += '<th class="cadena-th-da">' + label + '</th>';
  }
  html += '<th class="cadena-th-result">LD DESC</th>';
  html += '<th class="cadena-th-result">LN DESC</th>';
  html += '<th class="cadena-th-result">DO DESC</th>';
  html += "</tr></thead><tbody>";

  entries.forEach(function (entry, entryIndex) {
    var row = Array.isArray(entry.row) ? entry.row.slice() : [];
    var normalized = limitCadenaPathColumns(row, maxPathCount);
    // Usar la key exacta del entry (ya contiene nodeId y rowKey correctos normalizados)
    var key = entry.key;
    var rowKey = entry.rowKey || cadenaRowKey(normalized);
    var entryId = entry.entryId || (key + "||" + entryIndex);
    var descFields = getCadenaDescriptionFields(entry);
    var rowStyle = entry.matched ? "background: #fef3c7;" : "";
    var nodeTag = String((entry.node && entry.node.tag) || "").toUpperCase();
    var highlightClass = "";
    if (nodeTag === "DO" || nodeTag === "DO_SYNTH" || nodeTag === "DO_TYPE_CONTENT") {
      highlightClass = " cadena-row-selected-do";
    } else if (nodeTag === "LN" || nodeTag === "LN0" || nodeTag === "LN_SYNTH") {
      highlightClass = " cadena-row-selected-ln";
    } else if (nodeTag === "LNODETYPE" || nodeTag === "LNodeType" || nodeTag === "LNTYPE") {
      highlightClass = " cadena-row-selected-lnodetype";
    }
    var rowClass = entry.matched ? " cadena-row-matched" : "";
    rowClass += highlightClass;
    html += "<tr" + rowClass + " style=\"" + rowStyle + "\">";
    html += "<td>" + esc(normalized[1] || "") + "</td>";
    html += "<td>" + esc(normalized[2] || "") + "</td>";
    html += "<td>" + esc(normalized[3] || "") + "</td>";
    html += "<td>" + esc(normalized[4] || "") + "</td>";
    html += "<td>" + esc(normalized[5] || "") + "</td>";
    html += "<td>" + esc(getDisplaySdoName(normalized[6] || "")) + "</td>";
    for (var j = 0; j < maxPathCount; j++) {
      var pathValue = normalized[7 + j] || "";
      html += "<td>" + esc(pathValue || "") + "</td>";
    }
    html += "<td>" + esc(normalized[normalized.length - 3] || "") + "</td>";
    html += "<td>" + esc(normalized[normalized.length - 2] || "") + "</td>";
    html += '<td class="cadena-td-result">' + esc(getCadenaPreviewResult(row)) + "</td>";
    html += '<td class="cadena-td-result">' + esc(descFields.ldDesc || "") + "</td>";
    html += '<td class="cadena-td-result">' + esc(descFields.lnDesc || "") + "</td>";
    html += '<td class="cadena-td-result">' + esc(descFields.doDesc || "") + "</td>";
    html += '<td class="cadena-td-action">';
    html += '<button type="button" class="cadena-row-remove" data-entry-id="' + esc(encodeURIComponent(entryId)) + '" data-row-key="' + esc(encodeURIComponent(rowKey)) + '" title="Eliminar fila uno por uno" aria-label="Eliminar fila uno por uno"><i class="fa-solid fa-xmark" aria-hidden="true"></i></button>';
    html += '</td>';
    html += "</tr>";
  });

  html += "</tbody></table></div>";
  return html;
}

function clearAllTreeSelection() {
  var tree = window._cachedJstree || (window._cachedJstree = (window.jQuery && window.jQuery("#jstree").length ? window.jQuery("#jstree").jstree(true) : null));
  if (tree && typeof tree.uncheck_all === "function") {
    try { tree.uncheck_all(); } catch (e) {}
  }

  treeSelectedNodes = {};
  treeSelectedOrder = [];
  cadenaExcludedRowKeys = {};
  if (typeof clearCadenaPreviewHiddenEntries === 'function') clearCadenaPreviewHiddenEntries();

  updateTreeSelectionDisplay(true);
  if (typeof syncTreeSelectionDebounced === "function") syncTreeSelectionDebounced();
  setStatus("Se eliminaron todos los elementos seleccionados del árbol.");
}

function updateTreeSelectionDisplay(forceEmpty) {
  var listDiv = document.getElementById("tree-selected-list");
  var summaryDiv = document.getElementById("tree-selection-summary");
  if (!listDiv) return;

  var selectedIds = sortTreeSelectedIds(Object.keys(treeSelectedNodes || {}));
  if (!selectedIds.length && !forceEmpty && currentNodeMeta && currentNodeMeta.nodeId) {
    selectedIds = [currentNodeMeta.nodeId];
  }

  // Usar versión optimizada con caché
  var entries = buildCadenaPreviewEntriesOptimized(selectedIds);

  function renderPreviewSummary(visibleCount) {
    if (!summaryDiv) return;
    summaryDiv.innerHTML =
      '<span style="background: rgba(15, 118, 110, 0.18); border: 1px solid rgba(45, 212, 191, 0.22); color: #ccfbf1; padding: 4px 8px; border-radius: 999px; font-size: 11px;">Nodos: ' + selectedIds.length + '</span>' +
      '<span style="background: rgba(30, 41, 59, 0.75); border: 1px solid rgba(148, 163, 184, 0.25); color: #e2e8f0; padding: 4px 8px; border-radius: 999px; font-size: 11px;">Filas vista previa: ' + visibleCount + '</span>';
  }

  renderPreviewSummary(entries.length);

  var tree = window._cachedJstree || (window._cachedJstree = $("#jstree").jstree(true));

  function clearTreeSelectionState() {
    if (tree && typeof tree.uncheck_all === 'function') {
      try { tree.uncheck_all(); } catch (e) {}
    }
    if (tree && typeof tree.deselect_all === 'function') {
      try { tree.deselect_all(true); } catch (e) {}
    }
    document.querySelectorAll('#jstree a.jstree-anchor').forEach(function (anchor) {
      anchor.classList.remove('tree-node-checked-highlight');
      anchor.classList.remove('jstree-clicked');
    });
    treeSelectedNodes = {};
    treeSelectedOrder = [];
  }

  if (selectedIds.length === 0) {
    clearTreeSelectionState();
    listDiv.innerHTML = renderCadenaPreviewTable([]);
    renderPreviewSummary(0);
    if (typeof applyTreeCheckedHighlights === 'function') applyTreeCheckedHighlights();
    return;
  }

  switchTab('excel');

  if (!entries.length) {
    clearTreeSelectionState();
    listDiv.innerHTML = renderCadenaPreviewTable([]);
    renderPreviewSummary(0);
    if (typeof applyTreeCheckedHighlights === 'function') applyTreeCheckedHighlights();
    return;
  }

  listDiv.innerHTML = renderCadenaPreviewTable(entries);
  renderPreviewSummary(listDiv.querySelectorAll(".cadena-preview-table tbody tr").length);

  listDiv.querySelectorAll(".cadena-row-remove").forEach(function (btn) {
    btn.addEventListener("click", function (e) {
      e.preventDefault();
      e.stopPropagation();
      var entryId = btn.getAttribute("data-entry-id") || "";
      var rowKey = btn.getAttribute("data-row-key") || "";
      var row = btn.closest("tr");
      if (row && row.parentNode) row.parentNode.removeChild(row);
      removeCadenaPreviewRow(decodeURIComponent(entryId), decodeURIComponent(rowKey));
    });
  });

  syncCadenaPreviewStickyHeader(listDiv);
  if (typeof applyTreeCheckedHighlights === 'function') applyTreeCheckedHighlights();
}

// Calcula la altura real de la primera fila del encabezado (LDINS/LN/DO/DA...)
// y la usa como "top" de la segunda fila (PREFIX/LNCLASS/.../BDA2) para que
// ambas filas queden perfectamente fijas (estáticas) al hacer scroll vertical,
// sin depender de un valor fijo en px que podría desajustarse con la fuente,
// el zoom del navegador o futuros cambios de estilo.
function syncCadenaPreviewStickyHeader(listDiv) {
  if (!listDiv) return;
  var firstRow = listDiv.querySelector(".cadena-preview-table thead tr.cadena-head-row:first-child");
  var subRow = listDiv.querySelector(".cadena-preview-table thead tr.cadena-head-row-sub");
  if (!firstRow || !subRow) return;

  var applyOffset = function () {
    var height = firstRow.getBoundingClientRect().height;
    if (height > 0) {
      subRow.querySelectorAll("th").forEach(function (th) {
        th.style.top = height + "px";
      });
    }
  };

  applyOffset();
  // Reaplicar tras el siguiente frame por si las fuentes/medidas aún no
  // estaban listas en el primer cálculo (p.ej. carga inicial de la página).
  if (window.requestAnimationFrame) {
    window.requestAnimationFrame(applyOffset);
  }
}

function removeCadenaPreviewRow(entryId, rowKey) {
  if (!entryId && !rowKey) return;

  if (typeof hideCadenaPreviewRow === 'function') {
    hideCadenaPreviewRow(entryId, rowKey);
  } else if (entryId && typeof hideCadenaPreviewEntry === 'function') {
    hideCadenaPreviewEntry(entryId);
  }

  var entryKey = entryId;
  var lastSeparator = entryId ? entryId.lastIndexOf("||") : -1;
  if (lastSeparator > -1) {
    entryKey = entryId.slice(0, lastSeparator);
  }
  if (entryKey) incrementCadenaExcludedRowCount(entryKey);
  if (rowKey) incrementCadenaExcludedRowCount(rowKey);

  if (typeof clearCadenaEntriesCache === 'function') clearCadenaEntriesCache();

  // Usar scheduleUpdateTreeSelectionDisplay para una actualización demorada que permite
  // que el DOM se procese correctamente y la fila desaparezca visualmente
  if (typeof scheduleUpdateTreeSelectionDisplay === 'function') {
    scheduleUpdateTreeSelectionDisplay();
  } else {
    updateTreeSelectionDisplay();
  }
  setStatus("Se eliminó una fila de la vista previa.");
}

// Ocultar una fila de la vista previa sin tocar el checkbox del árbol.
function removeCadenaPreviewRowOnly(key) {
  if (!key) return;

  // Marcar solo la huella de contenido para ocultar una ocurrencia idéntica.
  incrementCadenaExcludedRowCount(key);

  // Limpiar caché de entradas para forzar recálculo inmediato
  if (typeof clearCadenaEntriesCache === 'function') clearCadenaEntriesCache();

  // Actualizar la vista sin desmarcar el nodo en el árbol
  updateTreeSelectionDisplay();
  setStatus("Se ocultó la fila de la vista previa (sin desmarcar en el árbol).");
}

function detectElementType(node) {
  var tag = String(node && node.tag ? node.tag : "").toUpperCase();
  var attrs = node && node.attrs ? node.attrs : {};
  var text = String(node && node.text ? node.text : "").trim();
  var name = String(attrs.name || attrs.doName || attrs.daName || attrs.iedName || "").trim();
  var typeHint = String(attrs.type || attrs.DOType || attrs.DAType || attrs.DataType || "").trim();

  if (tag === "IED" || /IED/i.test(name)) return "IED";
  if (tag === "LDEVICE" || /LDEVICE/i.test(name)) return "LDevice";
  if (tag === "LN" || tag === "LN0" || /LN/i.test(name)) return "LN";
  if (tag === "DO" || tag === "DO_SYNTH" || /DO/i.test(name) || /DOType/i.test(typeHint) || /\bDO\b/i.test(text)) return "DO";
  if (tag === "DA" || tag === "DA_SYNTH" || /DA/i.test(name) || /DAType/i.test(typeHint) || /\bDA\b/i.test(text)) return "DA";
  if (tag === "FCDA") return "FCDA";
  if (tag === "DATASET") return "Dataset";
  return tag || "Nodo";
}

function getElementColor(type) {
  var palette = {
    IED: "FFE0F2FE",
    LDevice: "FFFDE68A",
    LN: "FFDBEAFE",
    DO: "FFD1FAE5",
    DA: "FFEDE9FE",
    FCDA: "FFFCE7F3",
    Dataset: "FFCCFBF1",
    Nodo: "FFE5E7EB",
  };
  return palette[type] || "FFE5E7EB";
}

function splitPathParts(value) {
  return String(value || "")
    .split(/[.\/\\>]+/)
    .map(function (part) { return part.trim(); })
    .filter(function (part) { return part; });
}

function formatNestedRoute(parentPath, label) {
  var parts = [parentPath, label].filter(function (part) {
    return String(part || "").trim();
  });
  return parts.join(" / ");
}

function appendBehSuffix(text, name) {
  var base = String(text || "");
  if (/^SE_/i.test(String(name || "")) && base && base.indexOf("Beh") === -1) {
    return base + " · Beh";
  }
  return base;
}

function looksLikeTechnicalId(value) {
  var text = String(value || "").trim();
  if (!text) return false;
  if (/^IED\d+_[A-Za-z0-9_]+_[A-Za-z0-9]{8,}$/i.test(text)) return true;
  return /_[A-Fa-f0-9]{8,}(?:_[A-Fa-f0-9]{4,}){2,}/.test(text) || /[A-Fa-f0-9]{24,}/.test(text);
}

function getReadableNodeLabel(node) {
  var attrs = node && node.attrs ? node.attrs : {};
  var candidates = [
    attrs.value,
    attrs.text,
    attrs.Val,
    attrs.val,
    attrs.name,
    attrs.doName,
    attrs.daName,
    node && node.label,
    node && node.text,
  ];

  for (var i = 0; i < candidates.length; i++) {
    var candidate = String(candidates[i] || "").trim();
    if (!candidate) continue;
    if (!looksLikeTechnicalId(candidate)) return candidate;
  }

  return String((node && node.text) || attrs.name || attrs.doName || attrs.daName || attrs.type || attrs.id || "").trim();
}

function stripVisibleTypePrefixes(value) {
  return String(value || "")
    .replace(/^\s*(?:Datatype|Contenido Datatype|Contenido DAType|SDO:|BDA:|DA:|DO:|LNodeType:|DOType:|DAType:)\s*/i, "")
    .replace(/\s*\[type=[^\]]+\]\s*$/i, "")
    .replace(/\s*\[fc=[^\]]+\]\s*$/i, "")
    .trim();
}

function getHierarchicalNameParts(value, fallback) {
  var raw = String(value || fallback || "");
  if (!raw) return ["", "", ""];

  var cleaned = raw
    .replace(/Contenido\s+DAType\s*:\s*[^\/.]+/gi, "")
    .replace(/Contenido\s+DAType\s+[^\s\/.]+/gi, "")
    .replace(/\b(LNodeType|DO|DA|BDA)\s*:\s*/gi, "")
    .replace(/\bDAType\s*:\s*[^\/.]+/gi, "")
    .replace(/\bDAType\s+[^\s\/.]+/gi, "")
    .replace(/\bDatatype\s*:\s*[^\/.]+/gi, "")
    .replace(/\bDatatype\s+[^\s\/.]+/gi, "")
    .replace(/\[fc\s*=\s*[^\]]+\]/gi, "")
    .replace(/\bfc\s*=\s*[a-z0-9_:-]+\b/gi, "")
    .replace(/[·|]/g, " ")
    .replace(/\s*\/\s*/g, "/")
    .replace(/[\s.]+/g, ".");

  var parts = splitPathParts(cleaned).filter(function (part) {
    var p = String(part || "").trim();
    if (!p) return false;
    if (/^(?:LNodeType|DO|DA|BDA|Contenido)$/i.test(p)) return false;
    if (/^(?:fc|btype|type)\s*=\s*/i.test(p)) return false;
    if (/^SE_.+_V\d+$/i.test(p)) return false;
    if (p.indexOf("_") !== -1 && p.length >= 18 && /_V\d+/i.test(p)) return false;
    return true;
  });

  return [parts[0] || "", parts[1] || "", parts[2] || ""];
}

function collectNestedSubtypeRows(node, baseRoute) {
  var rows = [];
  if (!node) return rows;

  var attrs = node.attrs || {};
  var tag = String(node.tag || "").toUpperCase();
  var route = baseRoute || "";

  if (tag === "DATATYPE" || tag === "DA_TYPE_CONTENT") {
    var daTypeId = attrs.type || attrs.id || "";
    if (daTypeId && daTypeIndex[daTypeId] && daTypeIndex[daTypeId].bdas) {
      daTypeIndex[daTypeId].bdas.forEach(function (bda) {
        var bdaRoute = route ? route + " / " + (bda.name || "") : (bda.name || "");
        rows.push({
          type: "DA",
          route: bdaRoute,
          visibleName: bda.name || "",
          attrs: Object.assign({ name: bda.name, fc: bda.fc, bType: bda.bType, type: bda.type }, bda.attrs || {}),
          tag: "BDA_SYNTH",
          ctx: node.ctx || {},
          parentPath: route,
        });
        if (isStructBdaEntry(bda) && bda.type && daTypeIndex[bda.type] && daTypeIndex[bda.type].bdas) {
          rows = rows.concat(collectNestedSubtypeRows({ tag: "BDA_SYNTH", attrs: Object.assign({ name: bda.name, fc: bda.fc, bType: bda.bType, type: bda.type }, bda.attrs || {}), ctx: node.ctx || {} }, bdaRoute));
        }
      });
    }
  }

  if (tag === "DA_SYNTH" && isStructDaEntry(attrs)) {
    var structDaTypeId = attrs.type || "";
    if (structDaTypeId && daTypeIndex[structDaTypeId] && daTypeIndex[structDaTypeId].bdas) {
      daTypeIndex[structDaTypeId].bdas.forEach(function (bda) {
        var bdaRoute = route ? route + " / " + (bda.name || "") : (bda.name || "");
        rows.push({
          type: "DA",
          route: bdaRoute,
          visibleName: bda.name || "",
          attrs: Object.assign({ name: bda.name, fc: bda.fc, bType: bda.bType, type: bda.type }, bda.attrs || {}),
          tag: "BDA_SYNTH",
          ctx: node.ctx || {},
          parentPath: route,
        });
        if (isStructBdaEntry(bda) && bda.type && daTypeIndex[bda.type] && daTypeIndex[bda.type].bdas) {
          rows = rows.concat(collectNestedSubtypeRows({ tag: "BDA_SYNTH", attrs: Object.assign({ name: bda.name, fc: bda.fc, bType: bda.bType, type: bda.type }, bda.attrs || {}), ctx: node.ctx || {} }, bdaRoute));
        }
      });
    }
  }

  if (tag === "DO_TYPE_CONTENT" || tag === "DO_SYNTH" || tag === "DO_TYPE_GROUP") {
    var doTypeId = attrs.type || attrs.id || "";
    if (doTypeId && doTypeIndex[doTypeId] && doTypeIndex[doTypeId].das) {
      doTypeIndex[doTypeId].das.forEach(function (da) {
        var daRoute = route ? route + " / DA: " + (da.name || "") : "DA: " + (da.name || "");
        rows.push({
          type: "DA",
          route: daRoute,
          visibleName: da.name || "",
          attrs: Object.assign({ name: da.name, fc: da.fc, bType: da.bType, type: da.type }, da.attrs || {}),
          tag: "DA_SYNTH",
          ctx: node.ctx || {},
          parentPath: route,
        });
      });
    }
  }

  return rows;
}

function getCadenaResultadoFormula(excelRow) {
  var r = excelRow;
  return (
    'CONCAT(B' + r + ',".",C' + r + ',D' + r + ',E' + r + ',".",IF(G' + r + '<>"",CONCAT(F' + r + ',".",G' + r + '),F' + r + '),".",IF(I' + r + '<>"",IF(J' + r + '<>"",CONCAT(H' + r + ',".",I' + r + ',".",J' + r + '),CONCAT(H' + r + ',".",I' + r + ')),H' + r + '))'
  );
}

function buildCadenaResultado(ldInst, prefix, lnClass, lnInst, doName, daG, daH, daI) {
  var result =
    String(ldInst || "") + "." + String(prefix || "") + String(lnClass || "") + String(lnInst || "") +
    "." + String(doName || "") + "." + String(daG || "");
  if (String(daH || "").trim() !== "") {
    result += "." + String(daH).trim();
    if (String(daI || "").trim() !== "") {
      result += "." + String(daI).trim();
    }
  }
  return result;
}

function parseDoNameFromParentPath(parentPath, currentName) {
  if (!parentPath) return "";

  var match = String(parentPath).match(/\bDO\s+([^\s/·]+)/i);
  if (match) return match[1].trim();

  var parts = String(parentPath)
    .split(/[\/·]+/)
    .map(function (part) { return part.trim(); })
    .filter(function (part) { return Boolean(part); });

  if (!parts.length) return "";

  if (currentName) {
    var normalizedCurrent = normalizeName(currentName);
    var lastPart = normalizeName(parts[parts.length - 1]);
    if (normalizedCurrent && lastPart === normalizedCurrent && parts.length > 1) {
      return parts[parts.length - 2];
    }
  }

  return parts.length > 1 ? parts[parts.length - 2] : "";
}

function parseSdoNameFromParentPath(parentPath, currentName) {
  if (!parentPath) return "";

  var match = String(parentPath).match(/\bSDO[:\s]+([^\s/·]+)/i);
  if (match) return match[1].trim();

  var parts = String(parentPath)
    .split(/[\/·]+/)
    .map(function (part) { return part.trim(); })
    .filter(function (part) { return Boolean(part); });

  if (!parts.length) return "";

  var suffix = parts[parts.length - 1];
  if (currentName && normalizeName(currentName) !== normalizeName(suffix) && /^SDO$/i.test(parts[parts.length - 2])) {
    return suffix;
  }

  var sdoIndex = parts.findIndex(function (part) { return /^SDO$/i.test(part); });
  return sdoIndex >= 0 && parts.length > sdoIndex + 1 ? parts[sdoIndex + 1] : "";
}

function enrichStoredTreeNode(stored, nodeId) {
  if (!stored) return stored;
  var fields = resolveSelectionFields(stored, nodeId);
  var resolvedLdDesc = getLdDescByInst(fields.ldInst);
  stored.attrs = Object.assign({}, stored.attrs || {}, {
    ldInst: fields.ldInst || stored.attrs.ldInst || "",
    prefix: fields.prefix || stored.attrs.prefix || "",
    lnClass: fields.lnClass || stored.attrs.lnClass || "",
    lnInst: fields.lnInst || stored.attrs.lnInst || "",
    doName: fields.doName || stored.attrs.doName || "",
    daName: fields.daName || stored.attrs.daName || "",
    lnType: fields.lnType || stored.attrs.lnType || "",
    DOType: fields.doTypeId || stored.attrs.DOType || "",
    ldDesc: resolvedLdDesc || stored.attrs.ldDesc || "",
  });
  stored.ctx = Object.assign({}, stored.ctx || {}, {
    ldInst: fields.ldInst || stored.ctx.ldInst || "",
    prefix: fields.prefix || stored.ctx.prefix || "",
    lnClass: fields.lnClass || stored.ctx.lnClass || "",
    lnInst: fields.lnInst || stored.ctx.lnInst || "",
    lnType: fields.lnType || stored.ctx.lnType || "",
    ldDesc: resolvedLdDesc || stored.ctx.ldDesc || "",
  });
  return stored;
}

function resolveSelectionFields(node, nodeId) {
  node = node || {};
  var attrs = node.attrs || {};
  var ctx = node.ctx || {};
  var tag = String(node.tag || "").toUpperCase();
  var fields = {
    ldInst: "",
    prefix: "",
    lnClass: "",
    lnInst: "",
    doName: "",
    lnType: "",
    doTypeId: "",
    daName: "",
    sdoName: "",
  };

  function mergeFromMeta(meta) {
    if (!meta) return;
    var a = meta.attrs || {};
    var c = meta.ctx || {};
    var t = String(meta.tag || "").toUpperCase();
    if (!fields.ldInst) {
      fields.ldInst = c.ldInst || c.lDeviceInst || a.ldInst || "";
    }
    if (!fields.prefix) fields.prefix = c.prefix || a.prefix || "";
    if (!fields.lnClass) fields.lnClass = c.lnClass || a.lnClass || "";
    if (!fields.lnInst) fields.lnInst = c.lnInst || a.lnInst || a.inst || "";
    if (!fields.lnType) {
      fields.lnType = c.lnType || a.lnType || a["lnType (CID)"] || "";
    }
    if (!fields.doName && c.doName) fields.doName = c.doName;
    if (!fields.sdoName && c.sdoName) fields.sdoName = c.sdoName;
    if (!fields.doTypeId) {
      fields.doTypeId =
        a.DOType ||
        ((t === "DO_SYNTH" || t === "DO_TYPE_CONTENT" || t === "DOTYPE") ? a.type || a.id : "") ||
        "";
    }
    if (!fields.doName && (t === "DO_SYNTH" || t === "DO" || t === "FCDA" || t === "DO_TYPE_CONTENT")) {
      fields.doName = a.doName || a.name || "";
    }
    if (!fields.doName && a.doName) {
      fields.doName = a.doName;
    }
    if (!fields.sdoName && (/^SDO(?:_SYNTH)?$/i.test(t) || t === "SDO")) {
      fields.sdoName = a.name || a.sdoName || "";
    }
    if (t === "FCDA") {
      fields.ldInst = a.ldInst || c.ldInst || fields.ldInst;
      fields.prefix = a.prefix || c.prefix || fields.prefix;
      fields.lnClass = a.lnClass || c.lnClass || fields.lnClass;
      fields.lnInst = a.lnInst || c.lnInst || fields.lnInst;
      fields.doName = a.doName || fields.doName;
      fields.daName = a.daName || fields.daName;
      fields.sdoName = a.sdoName || fields.sdoName;
      fields.doTypeId = a.DOType || fields.doTypeId;
      fields.lnType = c.lnType || a.lnType || fields.lnType;
    }
    if (t === "LN" || t === "LN0" || t === "LN_SYNTH") {
      if (!fields.ldInst) fields.ldInst = c.ldInst || c.lDeviceInst || a.ldInst || fields.ldInst;
      fields.prefix = c.prefix || a.prefix || fields.prefix;
      fields.lnClass = c.lnClass || a.lnClass || fields.lnClass;
      fields.lnInst = c.lnInst || a.inst || a.lnInst || fields.lnInst;
      fields.lnType = c.lnType || a.lnType || fields.lnType;
    }
    if (t === "LNODETYPE") {
      fields.lnType = a.id || fields.lnType;
      if (!fields.lnClass) fields.lnClass = a.lnClass || "";
    }
  }

  var tree = window._cachedJstree || (window._cachedJstree = (window.jQuery && window.jQuery("#jstree").length ? window.jQuery("#jstree").jstree(true) : null));
  if (tree && nodeId) {
    var jstreeNode = tree.get_node(nodeId);
    var parentIds = jstreeNode && jstreeNode.parents ? jstreeNode.parents : node.parentIds || [];
    parentIds.forEach(function (pid) {
      if (!pid || pid === "#") return;
      var parentNode = tree.get_node(pid);
      if (parentNode && parentNode.original && parentNode.original._meta) {
        mergeFromMeta(parentNode.original._meta);
      }
    });
  } else if (node.parentIds && node.parentIds.length) {
    node.parentIds.forEach(function (pid) {
      var stored = treeSelectedNodes[pid];
      if (stored) {
        mergeFromMeta({ tag: stored.tag, attrs: stored.attrs, ctx: stored.ctx });
      }
    });
  }

  mergeFromMeta({ tag: tag, attrs: attrs, ctx: ctx });

  if (!fields.doName) fields.doName = parseDoNameFromParentPath(node.parentPath, attrs.daName || attrs.name || "");
  if (!fields.sdoName) fields.sdoName = parseSdoNameFromParentPath(node.parentPath, attrs.name || "");
  if (!fields.daName) {
    fields.daName = attrs.daName || ((tag === "DA_SYNTH" || tag === "BDA_SYNTH") ? attrs.name : "") || "";
  }
  if (!fields.lnClass && fields.lnType && lnodeTypeIndex[fields.lnType]) {
    fields.lnClass = lnodeTypeIndex[fields.lnType].lnClass || fields.lnClass;
  }
  if (!fields.lnType && attrs.lnType) fields.lnType = attrs.lnType;
  if (tag === "DO_SYNTH") {
    if (attrs.name && !fields.doName) fields.doName = attrs.name;
    if (attrs.type) fields.doTypeId = attrs.type;
    if (attrs.lnType) {
      fields.lnType = attrs.lnType;
      if (!fields.lnClass && lnodeTypeIndex[attrs.lnType]) {
        fields.lnClass = lnodeTypeIndex[attrs.lnType].lnClass || "";
      }
    }
  }

  return fields;
}

function resolveCadenaBase(node, nodeId) {
  var fields = resolveSelectionFields(node, nodeId);
  return {
    ldInst: fields.ldInst,
    prefix: fields.prefix,
    lnClass: fields.lnClass,
    lnInst: fields.lnInst,
    doName: fields.doName,
    lnType: fields.lnType,
    doTypeId: fields.doTypeId,
    daName: fields.daName,
    sdoName: fields.sdoName,
  };
}

function enrichCadenaBaseFromAncestors(base, nodeId, attrs, ctx) {
  var enriched = Object.assign({}, base || {});
  attrs = attrs || {};
  ctx = ctx || {};

  if (nodeId) {
    var doMeta = getAncestorMetaByTags(nodeId, ["DO_SYNTH", "DO"]);
    var sdoMeta = getAncestorMetaByTags(nodeId, ["SDO_SYNTH", "SDO"]);
    var lnTypeMeta = getAncestorMetaByTags(nodeId, ["LNODETYPE"]);
    var lnMeta = getAncestorMetaByTags(nodeId, ["LN_SYNTH", "LN", "LN0"]);

    if (doMeta && doMeta.attrs) {
      if (!enriched.doName) enriched.doName = doMeta.attrs.doName || doMeta.attrs.name || "";
      if (!enriched.doTypeId) {
        enriched.doTypeId = doMeta.attrs.type || doMeta.attrs.DOType || doMeta.attrs.id || "";
      }
    }
    if (sdoMeta && sdoMeta.attrs) {
      if (!enriched.sdoName) enriched.sdoName = sdoMeta.attrs.name || sdoMeta.attrs.sdoName || "";
    }
    if (lnTypeMeta && lnTypeMeta.attrs) {
      if (!enriched.lnType) enriched.lnType = lnTypeMeta.attrs.id || lnTypeMeta.attrs.lnType || "";
      if (!enriched.lnClass) enriched.lnClass = lnTypeMeta.attrs.lnClass || enriched.lnClass || "";
    }
    if (lnMeta) {
      var la = lnMeta.attrs || {};
      var lc = lnMeta.ctx || {};
      if (!enriched.ldInst) enriched.ldInst = la.ldInst || lc.ldInst || lc.lDeviceInst || "";
      if (!enriched.prefix) enriched.prefix = la.prefix || lc.prefix || enriched.prefix || "";
      if (!enriched.lnClass) enriched.lnClass = la.lnClass || lc.lnClass || enriched.lnClass || "";
      if (!enriched.lnInst) enriched.lnInst = la.lnInst || lc.lnInst || la.inst || enriched.lnInst || "";
      if (!enriched.lnType) enriched.lnType = la.lnType || lc.lnType || enriched.lnType || "";
    }
  }

  if (!enriched.doName) enriched.doName = attrs.doName || ctx.doName || "";
  if (!enriched.sdoName) enriched.sdoName = attrs.sdoName || ctx.sdoName || "";
  if (!enriched.lnType) enriched.lnType = attrs.lnType || ctx.lnType || "";
  if (!enriched.ldInst) enriched.ldInst = attrs.ldInst || ctx.ldInst || ctx.lDeviceInst || "";
  if (!enriched.prefix) enriched.prefix = attrs.prefix || ctx.prefix || "";
  if (!enriched.lnClass) enriched.lnClass = attrs.lnClass || ctx.lnClass || "";
  if (!enriched.lnInst) enriched.lnInst = attrs.lnInst || ctx.lnInst || attrs.inst || "";
  if (!enriched.doTypeId) enriched.doTypeId = resolveCadenaDoTypeId(enriched);

  if (enriched.doName && enriched.lnType) {
    enriched = enrichCadenaBaseFromFcda(
      enriched,
      enriched.doName,
      enriched.lnType,
      enriched.doTypeId || ""
    );
  }

  // Si después de buscar ancestros todavía falta el contexto de rama (LD, LN),
  // intentamos recuperarlo usando el lnType por defecto si está disponible.
  if ((!enriched.ldInst || !enriched.lnClass) && enriched.lnType) {
    var defaultCtx = getDefaultLnContextForType(enriched.lnType);
    if (defaultCtx) {
      if (!enriched.ldInst) enriched.ldInst = defaultCtx.ldInst || "";
      if (!enriched.prefix) enriched.prefix = defaultCtx.prefix || "";
      if (!enriched.lnClass) enriched.lnClass = defaultCtx.lnClass || "";
      if (!enriched.lnInst) enriched.lnInst = defaultCtx.lnInst || "";
    }
  }

  return enriched;
}

function resolveCadenaDoTypeId(base) {
  if (base.doTypeId && doTypeIndex[base.doTypeId]) return base.doTypeId;
  if (base.lnType && base.doName && lnodeTypeIndex[base.lnType]) {
    var entry = findNamedEntry(lnodeTypeIndex[base.lnType].dos, base.doName);
    if (entry && entry.type) return entry.type;
  }
  return "";
}

function enrichCadenaBaseFromFcda(base, doName, lnTypeId, doTypeId) {
  var enriched = Object.assign({}, base || {});
  var bestFcdaMatch = findBestFcdaMatch(doName, lnTypeId, enriched, lnRecords, doTypeId);
  var matchingFcda = bestFcdaMatch && bestFcdaMatch.rec ? bestFcdaMatch.rec : null;
  if (!matchingFcda) return enriched;
  return Object.assign(enriched, {
    ldInst: enriched.ldInst || matchingFcda.LDInst || "",
    prefix: enriched.prefix || matchingFcda.Prefix || "",
    lnClass: enriched.lnClass || matchingFcda.LNClass || "",
    lnInst: enriched.lnInst || matchingFcda.LNInst || "",
    lnType: enriched.lnType || matchingFcda.LNodeType || lnTypeId || "",
    doTypeId: enriched.doTypeId || matchingFcda.DOType || doTypeId || "",
  });
}

function buildCadenaRowsFromLnTypeDos(base, lnTypeId) {
  var rows = [];
  if (!lnTypeId || !lnodeTypeIndex[lnTypeId]) return rows;
  var lnt = lnodeTypeIndex[lnTypeId];
  var scopeBase = Object.assign({}, base || {});
  if (!scopeBase.lnClass && lnt.lnClass) scopeBase.lnClass = lnt.lnClass;
  if (!scopeBase.lnType) scopeBase.lnType = lnTypeId;

  (lnt.dos || []).forEach(function (doEntry) {
    var doName = doEntry.name || "";
    var doTypeId = doEntry.type || "";
    if (!doName || !doTypeId) return;
    var doBase = enrichCadenaBaseFromFcda(
      Object.assign({}, scopeBase, { doName: doName, doTypeId: doTypeId }),
      doName,
      lnTypeId,
      doTypeId
    );
    expandDoTypeToCadenaRows(doBase, doName, doTypeId).forEach(function (row) {
      rows.push(row);
    });
  });

  return rows;
}

function buildCadenaRowsFromLNodeTypeNode(node, nodeId, base) {
  var rows = [];
  var attrs = (node && node.attrs) || {};
  var lnTypeId = attrs.id || base.lnType || "";
  if (!lnTypeId) return rows;

  var tree = window._cachedJstree || (window._cachedJstree = (window.jQuery && window.jQuery("#jstree").length ? window.jQuery("#jstree").jstree(true) : null));
  var jstreeNode = tree && nodeId ? tree.get_node(nodeId) : null;
  var lnChildren = [];

  if (jstreeNode && Array.isArray(jstreeNode.children)) {
    jstreeNode.children.forEach(function (childId) {
      var child = tree.get_node(childId);
      if (!child || !child.original || !child.original._meta) return;
      if (String(child.original._meta.tag || "").toUpperCase() === "LN_SYNTH") {
        lnChildren.push(child);
      }
    });
  }

  if (lnChildren.length) {
    lnChildren.forEach(function (lnChild) {
      var lnMeta = lnChild.original._meta || {};
      var lnAttrs = lnMeta.attrs || {};
      var lnCtx = lnMeta.ctx || {};
      var lnBase = Object.assign({}, base, {
        ldInst: lnAttrs.ldInst || lnCtx.ldInst || base.ldInst || "",
        prefix: lnAttrs.prefix || lnCtx.prefix || base.prefix || "",
        lnClass: lnAttrs.lnClass || lnCtx.lnClass || base.lnClass || "",
        lnInst: lnAttrs.lnInst || lnCtx.lnInst || base.lnInst || "",
        lnType: lnAttrs.lnType || lnCtx.lnType || lnTypeId,
      });
      buildCadenaRowsFromLnTypeDos(lnBase, lnTypeId).forEach(function (row) {
        rows.push(row);
      });
    });
    return rows;
  }

  return buildCadenaRowsFromLnTypeDos(base, lnTypeId);
}

/** Columnas DA del Excel: G = <DA name> del DOType; H/I = BDA del DAType (anidado). */
function expandDaToCadenaPaths(daDef) {
  var daFromDoType = (daDef && daDef.name) || "";
  if (!daDef || !isStructDaEntry(daDef)) {
    return [{ daFromDoType: daFromDoType, dataTypeG: "", dataTypeH: "", bType: daDef && daDef.bType ? daDef.bType : "", fc: daDef && daDef.fc ? daDef.fc : "" }];
  }

  var paths = [];
  var typeDef = (daDef.type && daTypeIndex[daDef.type]) || null;
  var das = (typeDef && typeDef.das) || [];
  var bdas = (typeDef && typeDef.bdas) || [];
  
  if (!das.length && !bdas.length) {
    // If type is not found in index, check if it looks like a type ID and return empty instead
    if (daDef.type && daDef.type.indexOf('_') !== -1 && daDef.type.length > 20) {
      return [{ daFromDoType: daFromDoType, dataTypeG: "", dataTypeH: "", bType: daDef.bType || "", fc: daDef.fc || "" }];
    }
    return [{ daFromDoType: daFromDoType, dataTypeG: "", dataTypeH: "", bType: daDef.bType || "", fc: daDef.fc || "" }];
  }

  // Procesar DA del DataType
  das.forEach(function (da) {
    if (isStructDaEntry(da) && da.type && daTypeIndex[da.type]) {
      var nested = daTypeIndex[da.type].bdas || [];
      if (nested.length) {
        nested.forEach(function (nb) {
          var dataTypeG = da.name || "";
          var dataTypeH = nb.name || "";
          paths.push({ daFromDoType: daFromDoType, dataTypeG: dataTypeG, dataTypeH: dataTypeH, bType: nb.bType || "", fc: nb.fc || da.fc || daDef.fc || "" });
        });
      } else {
        var dataTypeG = da.name || "";
        paths.push({ daFromDoType: daFromDoType, dataTypeG: dataTypeG, dataTypeH: "", bType: da.bType || "", fc: da.fc || daDef.fc || "" });
      }
    } else {
      var dataTypeG = da.name || "";
      paths.push({ daFromDoType: daFromDoType, dataTypeG: dataTypeG, dataTypeH: "", bType: da.bType || "", fc: da.fc || daDef.fc || "" });
    }
  });

  // Procesar BDA del DataType
  bdas.forEach(function (bda) {
    if (isStructBdaEntry(bda) && bda.type && daTypeIndex[bda.type]) {
      var nested = daTypeIndex[bda.type].bdas || [];
      if (nested.length) {
        nested.forEach(function (nb) {
          var dataTypeG = bda.name || "";
          var dataTypeH = nb.name || "";
          paths.push({ daFromDoType: daFromDoType, dataTypeG: dataTypeG, dataTypeH: dataTypeH, bType: nb.bType || "", fc: nb.fc || bda.fc || daDef.fc || "" });
        });
      } else {
        var dataTypeG = bda.name || "";
        paths.push({ daFromDoType: daFromDoType, dataTypeG: dataTypeG, dataTypeH: "", bType: bda.bType || "", fc: bda.fc || daDef.fc || "" });
      }
    } else {
      var dataTypeG = bda.name || "";
      paths.push({ daFromDoType: daFromDoType, dataTypeG: dataTypeG, dataTypeH: "", bType: bda.bType || "", fc: bda.fc || daDef.fc || "" });
    }
  });

  return paths;
}

function buildCadenaDataRow(base, doName, doTypeId, sdoName, daName, dataTypeG, dataTypeH, bType, fc) {
  var row = [""];
  row.push(base.ldInst || "");
  row.push(base.prefix || "");
  row.push(base.lnClass || "");
  row.push(base.lnInst || "");
  row.push(doName || "");
  row.push(sdoName || "");
  row.push(daName || "");
  row.push(dataTypeG || "");
  row.push(dataTypeH || "");
  row.push(bType || "");
  row.push(fc || "");
  if (sdoName) {
    row.push(
      buildCadenaHierarchicalResult(
        base,
        doName || "",
        sdoName || "",
        [daName, dataTypeG, dataTypeH].filter(Boolean)
      )
    );
  } else {
    row.push(
      buildCadenaResultado(
        base.ldInst || "",
        base.prefix || "",
        base.lnClass || "",
        base.lnInst || "",
        doName || "",
        daName || "",
        dataTypeG || "",
        dataTypeH || ""
      )
    );
  }
  return row;
}

function buildCadenaHierarchicalResult(base, doName, sdoName, pathParts) {
  var prefix = String(base.prefix || "");
  var root = String(base.ldInst || "") + "." + prefix + String(base.lnClass || "") + String(base.lnInst || "");
  var path = [];
  if (doName) path.push(doName);
  if (sdoName) path.push(sdoName);
  if (Array.isArray(pathParts)) path = path.concat(pathParts.filter(Boolean));
  return root + (path.length ? "." + path.join(".") : "");
}

function buildCadenaHierarchicalRow(base, doName, sdoName, pathParts, bType, fc) {
  var row = [""];
  row.push(base.ldInst || "");
  row.push(base.prefix || "");
  row.push(base.lnClass || "");
  row.push(base.lnInst || "");
  row.push(doName || "");
  row.push(sdoName || "");
  (Array.isArray(pathParts) ? pathParts : []).forEach(function (part) {
    row.push(part || "");
  });
  row.push(bType || "");
  row.push(fc || "");
  row.push(buildCadenaHierarchicalResult(base, doName, sdoName, pathParts || []));
  return row;
}

function resolveDoTypeIdForFcda(base, doName) {
  var candidate = resolveCadenaDoTypeId(base);
  if (candidate) return candidate;
  if (!doName || !base.lnType || !lnodeTypeIndex[base.lnType]) return "";
  var entry = findNamedEntry(lnodeTypeIndex[base.lnType].dos, doName);
  return entry && entry.type ? entry.type : "";
}

function expandCadenaValue(base, doName, sdoName, element, remainingPath, segments) {
  if (!element) return [buildCadenaHierarchicalRow(base, doName, sdoName, segments || [])];
  if (remainingPath && remainingPath.length) {
    var typeDef = getDaTypeDef(element.type);
    if (typeDef) return expandCadenaPathInType(base, doName, sdoName, typeDef, remainingPath, segments || []);
    return [buildCadenaHierarchicalRow(base, doName, sdoName, (segments || []).concat(remainingPath), element.bType || "", element.fc || "")];
  }
  if (element.type && isStructDaEntry(element)) {
    var daTypeDef = getDaTypeDef(element.type);
    if (daTypeDef) return expandCadenaTypeChildren(base, doName, sdoName, daTypeDef, segments || []);
  }
  return [buildCadenaHierarchicalRow(base, doName, sdoName, segments || [], element.bType || "", element.fc || "")];
}

function expandCadenaPathInType(base, doName, sdoName, typeDef, pathParts, segments) {
  if (!typeDef) return [];
  if (!Array.isArray(pathParts) || !pathParts.length) {
    return expandCadenaTypeChildren(base, doName, sdoName, typeDef, segments || []);
  }

  var nextName = pathParts[0];
  var rest = pathParts.slice(1);

  if (typeDef.sdos && typeDef.sdos.length) {
    var sdo = findNamedEntry(typeDef.sdos, nextName);
    if (sdo) {
      var childType = getDoTypeDef(sdo.type);
      if (childType) return expandCadenaPathInType(base, doName, sdo.name, childType, rest, []);
      return [buildCadenaHierarchicalRow(base, doName, sdo.name, rest)];
    }
  }

  if (typeDef.das && typeDef.das.length) {
    var da = findNamedEntry(typeDef.das, nextName);
    if (da) return expandCadenaValue(base, doName, sdoName, da, rest, (segments || []).concat([da.name]));
  }

  if (typeDef.bdas && typeDef.bdas.length) {
    var bda = findNamedEntry(typeDef.bdas, nextName);
    if (bda) return expandCadenaValue(base, doName, sdoName, bda, rest, (segments || []).concat([bda.name]));
  }

  return [buildCadenaHierarchicalRow(base, doName, sdoName, (segments || []).concat(pathParts))];
}

function expandCadenaTypeChildren(base, doName, sdoName, typeDef, segments) {
  var rows = [];
  if (typeDef.das && typeDef.das.length) {
    typeDef.das.forEach(function (da) {
      rows = rows.concat(expandCadenaValue(base, doName, sdoName, da, [], (segments || []).concat([da.name])));
    });
  }
  if (typeDef.sdos && typeDef.sdos.length) {
    typeDef.sdos.forEach(function (sdo) {
      var childType = getDoTypeDef(sdo.type);
      if (childType) {
        rows = rows.concat(expandCadenaTypeChildren(base, doName, sdo.name, childType, []));
      } else {
        rows.push(buildCadenaHierarchicalRow(base, doName, sdo.name, []));
      }
    });
  }
  if (typeDef.bdas && typeDef.bdas.length) {
    typeDef.bdas.forEach(function (bda) {
      rows = rows.concat(expandCadenaValue(base, doName, sdoName, bda, [], (segments || []).concat([bda.name])));
    });
  }
  if (!rows.length) {
    rows.push(buildCadenaHierarchicalRow(base, doName, sdoName, segments || []));
  }
  return rows;
}

function buildCadenaRowsFromFcda(base, doName, daPath, lnType) {
  doName = doName || base.doName || "";
  var doTypeId = resolveDoTypeIdForFcda(base, doName);
  var doTypeDef = getDoTypeDef(doTypeId);
  var pathParts = String(daPath || "").split(".").filter(Boolean);
  if (!doTypeDef) {
    return [buildCadenaHierarchicalRow(base, doName, base.sdoName || "", pathParts)];
  }
  return expandCadenaPathInType(base, doName, "", doTypeDef, pathParts, []);
}

function expandDoTypeToCadenaRows(base, doName, doTypeId, currentSdo) {
  var rows = [];
  var seen = {};
  var activeTypes = {};

  function pushRow(row) {
    var key = cadenaRowKey(row);
    if (seen[key]) return;
    seen[key] = true;
    rows.push(row);
  }

  function pushDaRows(da, currentSdo) {
    expandDaToCadenaPaths(da).forEach(function (path) {
      pushRow(
        buildCadenaHierarchicalRow(
          base,
          doName,
          currentSdo || "",
          [path.daFromDoType, path.dataTypeG, path.dataTypeH].filter(Boolean),
          path.bType || "",
          path.fc || ""
        )
      );
    });
  }

  function expandTypeRecursive(typeId, currentSdoName) {
    var normalizedTypeId = String(typeId || "");
    if (!normalizedTypeId || activeTypes[normalizedTypeId]) return;

    var typeDef = getDoTypeDef(normalizedTypeId);
    if (!typeDef) return;

    activeTypes[normalizedTypeId] = true;

    if (typeDef.das && typeDef.das.length) {
      typeDef.das.forEach(function (da) {
        pushDaRows(da, currentSdoName);
      });
    }

    if (typeDef.sdos && typeDef.sdos.length) {
      typeDef.sdos.forEach(function (sdo) {
        var sdoPath = currentSdoName ? currentSdoName + "." + (sdo.name || "") : (sdo.name || "");
        var childTypeId = sdo.type || "";
        var childTypeDef = getDoTypeDef(childTypeId);

        if (childTypeDef && !activeTypes[String(childTypeId || "")]) {
          expandTypeRecursive(childTypeId, sdoPath);
        } else if (childTypeDef && activeTypes[String(childTypeId || "")]) {
          pushRow(buildCadenaHierarchicalRow(base, doName, sdoPath, []));
        } else {
          pushRow(buildCadenaHierarchicalRow(base, doName, sdoPath, []));
        }
      });
    }

    delete activeTypes[normalizedTypeId];
  }

  expandTypeRecursive(doTypeId, base.sdoName || "");
  return rows;
}

function cadenaRowKey(row) {
  if (!Array.isArray(row)) return "";
  return row
    .slice(1)
    .map(function (value) {
      return value == null ? "" : String(value);
    })
    .join("\u0001");
}

function limitCadenaPathColumns(row, maxPathCount) {
  var values = Array.isArray(row) ? row.slice() : [];
  var maxPaths = Math.max(0, Number(maxPathCount || 0));
  if (!values.length) return values;

  var fixedStart = values.slice(0, 7);
  var fixedEnd = values.slice(-3);
  var pathValues = values.slice(7, Math.max(7, values.length - 3));

  if (pathValues.length > maxPaths) {
    pathValues = pathValues.slice(0, maxPaths);
  }
  while (pathValues.length < maxPaths) {
    pathValues.push("");
  }

  return fixedStart.concat(pathValues, fixedEnd);
}

function getCadenaPathCountFromRow(row) {
  if (!Array.isArray(row) || row.length <= 10) return 0;
  return Math.max(0, row.length - 10);
}

function getCadenaMaxPathCountFromRows(rows) {
  var maxPathCount = 0;
  (rows || []).forEach(function (row) {
    var pathCount = getCadenaPathCountFromRow(row);
    if (pathCount > maxPathCount) maxPathCount = pathCount;
  });
  return maxPathCount;
}

function cadenaDoScopeKey(base, doName) {
  return [base.ldInst, base.prefix, base.lnClass, base.lnInst, doName || base.doName].join("\u0001");
}

function buildCadenaRowsFromLnRecord(record) {
  if (!record) return [];
  var base = {
    ldInst: record.LDInst || "",
    prefix: record.Prefix || "",
    lnClass: record.LNClass || "",
    lnInst: record.LNInst || "",
    doName: record.DOName || "",
    lnType: record.LNodeType || "",
    doTypeId: record.DOType || "",
  };
  var doTypeId = resolveCadenaDoTypeId(base);
  if (!doTypeId) return [];
  return expandDoTypeToCadenaRows(base, record.DOName, doTypeId);
}

function buildCadenaRowFromNode(node, nodeId) {
  var rows = buildCadenaRowsFromNode(node, nodeId);
  var base = resolveCadenaBase(node || {}, nodeId);
  return rows.length ? rows[0] : buildCadenaDataRow(base, "", "", "", "", "", "");
}

function getAncestorMetaByTags(nodeId, allowedTags) {
  var tags = Array.isArray(allowedTags) ? allowedTags.map(function (tag) {
    return String(tag || "").toUpperCase();
  }) : [];
  if (!nodeId || !tags.length) return null;

  var tree = window._cachedJstree || (window._cachedJstree = (window.jQuery && window.jQuery("#jstree").length ? window.jQuery("#jstree").jstree(true) : null));
  if (!tree) return null;

  var currentNode = tree.get_node(nodeId);
  var parentId = currentNode ? currentNode.parent : null;

  while (parentId && parentId !== "#") {
    var parentNode = tree.get_node(parentId);
    var parentMeta = parentNode && parentNode.original ? parentNode.original._meta : null;
    var parentTag = String(parentMeta && parentMeta.tag ? parentMeta.tag : "").toUpperCase();
    if (parentMeta && tags.indexOf(parentTag) !== -1) return parentMeta;
    parentId = parentNode ? parentNode.parent : null;
  }

  return null;
}

function getAncestorMetasByTags(nodeId, allowedTags) {
  var tags = Array.isArray(allowedTags) ? allowedTags.map(function (tag) {
    return String(tag || "").toUpperCase();
  }) : [];
  var result = [];
  if (!nodeId || !tags.length) return result;

  var tree = window._cachedJstree || (window._cachedJstree = (window.jQuery && window.jQuery("#jstree").length ? window.jQuery("#jstree").jstree(true) : null));
  if (!tree) return result;

  var currentNode = tree.get_node(nodeId);
  var parentId = currentNode ? currentNode.parent : null;

  while (parentId && parentId !== "#") {
    var parentNode = tree.get_node(parentId);
    var parentMeta = parentNode && parentNode.original ? parentNode.original._meta : null;
    var parentTag = String(parentMeta && parentMeta.tag ? parentMeta.tag : "").toUpperCase();
    if (parentMeta && tags.indexOf(parentTag) !== -1) {
      result.unshift(parentMeta);
    }
    parentId = parentNode ? parentNode.parent : null;
  }

  return result;
}

function buildCadenaRowsFromNode(node, nodeId) {
  node = node || {};
  var tag = String(node.tag || "").toUpperCase();
  var attrs = node.attrs || {};
  var ctx = node.ctx || {};
  var base = resolveCadenaBase(node, nodeId);
  var doTypeId = resolveCadenaDoTypeId(base);

  // Omitimos el retorno temprano de DATATYPE para permitir que la lógica de expansión recursiva posterior se ejecute.
  // Esto asegura que al seleccionar un DAType o DA_TYPE_CONTENT, se muestren todos sus elementos internos
  // con el contexto completo de la rama (IED, LD, LN, DO).

  if (tag === "LN_SYNTH") {
    var lnTypeId = attrs.lnType || ctx.lnType || base.lnType || "";
    var lnBase = Object.assign({}, base, {
      ldInst: attrs.ldInst || ctx.ldInst || base.ldInst || "",
      prefix: attrs.prefix || ctx.prefix || base.prefix || "",
      lnClass: attrs.lnClass || ctx.lnClass || base.lnClass || "",
      lnInst: attrs.lnInst || ctx.lnInst || base.lnInst || "",
      lnType: lnTypeId,
    });
    if (!lnBase.lnClass && lnTypeId && lnodeTypeIndex[lnTypeId]) {
      lnBase.lnClass = lnodeTypeIndex[lnTypeId].lnClass || "";
    }
    return buildCadenaRowsFromLnTypeDos(lnBase, lnTypeId);
  }

  if (tag === "LNODETYPE") {
    return buildCadenaRowsFromLNodeTypeNode(node, nodeId, base);
  }

  var containerTags = [
    "LNTYPE_GROUP",
    "LDEVICE",
    "IED",
    "LN",
    "LN0",
    "DOTYPE",
    "DATATYPE",
    "DATYPE",
    "ENUMTYPE",
    "ENUMTYPE_GROUP",
    "FCDA_GROUP",
    "DOTYPE_GROUP"
  ];
  if (containerTags.indexOf(tag) >= 0) {
    return [];
  }

  // Si el nodo es un DO (o variante) perteneciente a un LNodeType y
  // existe un registro FCDA con el mismo DOName y DAName,
  // completar las celdas vacías LDInst, Prefix y LNInst desde el FCDA.
  var doName = base.doName || attrs.doName || attrs.name || "";
  var daName = attrs.daName || attrs.name || "";
  
  // Check if DO is within LNodeType by checking parent hierarchy
  var isUnderLNodeType = false;
  if (nodeId) {
    var jstreeInstance = window._cachedJstree || (window._cachedJstree = $("#jstree").jstree(true));
    if (jstreeInstance) {
      var currentTreeNode = jstreeInstance.get_node(nodeId);
      var parentNode = currentTreeNode ? jstreeInstance.get_node(currentTreeNode.parent) : null;
      while (parentNode && parentNode.id && parentNode.id !== "#") {
        var parentMeta = parentNode.original && parentNode.original._meta;
        if (parentMeta) {
          var parentTag = String(parentMeta.tag || "").toUpperCase();
          if (parentTag === "LNODETYPE" || parentTag === "LN_SYNTH" || parentTag === "LNTYPE_GROUP") {
            isUnderLNodeType = true;
            break;
          }
        }
        parentNode = jstreeInstance.get_node(parentNode.parent);
      }
    }
  }
  
  if ((tag === "DO" || tag === "DO_SYNTH" || tag === "DO_TYPE_CONTENT") && isUnderLNodeType && doName) {
    var bestFcdaMatch = findBestFcdaMatch(
      doName,
      attrs.lnType || ctx.lnType || base.lnType || "",
      ctx,
      lnRecords,
      attrs.DOType || attrs.type || base.doTypeId || doTypeId || ""
    );
    var matchingFcda = bestFcdaMatch && bestFcdaMatch.rec ? bestFcdaMatch.rec : null;

    if (matchingFcda) {
      if (!base.ldInst && matchingFcda.LDInst) base.ldInst = matchingFcda.LDInst;
      if (!base.prefix && matchingFcda.Prefix) base.prefix = matchingFcda.Prefix;
      if (!base.lnInst && matchingFcda.LNInst) base.lnInst = matchingFcda.LNInst;
      if (!base.lnClass && matchingFcda.LNClass) base.lnClass = matchingFcda.LNClass;
    }
  }

  if (tag === "FCDA") {
    var daName = attrs.daName || attrs.name || base.daName || "";
    var doName = attrs.doName || attrs.name || base.doName || "";
    var lnType = attrs.lnType || base.lnType || "";
    
    // For FCDA, ensure base has LDInst, Prefix, LnInst from attrs if available
    if (!base.ldInst && attrs.ldInst) base.ldInst = attrs.ldInst;
    if (!base.prefix && attrs.prefix) base.prefix = attrs.prefix;
    if (!base.lnClass && attrs.lnClass) base.lnClass = attrs.lnClass;
    if (!base.lnInst && attrs.lnInst) base.lnInst = attrs.lnInst;
    
    return buildCadenaRowsFromFcda(base, doName, daName, lnType);
  }

  if (tag === "DO_SYNTH" || tag === "DO") {
    // Enriquecer base con contexto del LN padre antes de expandir
    var enrichedBase = enrichCadenaBaseFromAncestors(base, nodeId, attrs, ctx);
    if (!enrichedBase.doName) enrichedBase.doName = base.doName || attrs.name || "";
    var resolvedDoTypeId = enrichedBase.doTypeId || doTypeId ||
      (enrichedBase.lnType && enrichedBase.doName ? resolveCadenaDoTypeId(enrichedBase) : "");

    if (resolvedDoTypeId) {
      var doRows = expandDoTypeToCadenaRows(enrichedBase, enrichedBase.doName, resolvedDoTypeId);
      if (doRows.length) return doRows;
    }
    // Fallback: siempre mostrar al menos una fila con los datos del DO
    return [buildCadenaDataRow(enrichedBase, enrichedBase.doName || attrs.name || "", resolvedDoTypeId || "", "", "", "", "", attrs.bType || "", attrs.fc || "")];
  }

  if (tag === "DO_TYPE_CONTENT") {
    var templateTypeId = attrs.id || doTypeId;
    if (templateTypeId) {
      var templateTypeDef = getDoTypeDef(templateTypeId);
      var templateCdc = templateTypeDef && templateTypeDef.cdc ? templateTypeDef.cdc : templateTypeId;
      var templateRows = expandDoTypeToCadenaRows(base, base.doName, templateTypeId);
      if (templateRows.length) return templateRows;
    }
  }

  if (tag === "SDO_SYNTH" || tag === "SDO") {
    var sdoTypeId = attrs.type || doTypeId || base.doTypeId || "";
    if (sdoTypeId) {
      var sdoBase = Object.assign({}, base, {
        sdoName: attrs.name || base.sdoName || "",
        doTypeId: sdoTypeId,
      });
      var sdoRows = expandDoTypeToCadenaRows(sdoBase, base.doName, sdoTypeId, sdoBase.sdoName);
      if (sdoRows.length) return sdoRows;
    }
    return [buildCadenaDataRow(base, base.doName, doTypeId, attrs.name || base.sdoName || "", "", "", "")];
  }

  if (tag === "DA_TYPE_CONTENT" || tag === "DATYPE") {
    base = enrichCadenaBaseFromAncestors(base, nodeId, attrs, ctx);
    var daTypeId = attrs.id || attrs.type || base.daTypeId || "";
    if (daTypeId) {
      var daTypeDef = getDaTypeDef(daTypeId);
      if (daTypeDef) {
        // Obtenemos el nombre del DA/BDA padre para mantener la jerarquía
        var daName = base.daName || "";
        if (!daName && nodeId) {
          var tree = window._cachedJstree || (window._cachedJstree = (window.jQuery && window.jQuery("#jstree").length ? window.jQuery("#jstree").jstree(true) : null));
          if (tree) {
            var nodeObj = tree.get_node(nodeId);
            var parentNode = nodeObj ? tree.get_node(nodeObj.parent) : null;
            var pMeta = parentNode && parentNode.original ? parentNode.original._meta : null;
            if (pMeta && pMeta.attrs) {
              daName = pMeta.attrs.name || pMeta.attrs.daName || "";
            }
          }
        }
        return expandCadenaTypeChildren(base, base.doName, base.sdoName || "", daTypeDef, daName ? [daName] : []);
      }
    }
    return [];
  }

  if (tag === "DA_SYNTH" || tag === "DA") {
    base = enrichCadenaBaseFromAncestors(base, nodeId, attrs, ctx);
    doTypeId = resolveCadenaDoTypeId(base);
    var daName = attrs.name || attrs.daName || base.daName || "";

    if (daName && base.doName && base.sdoName) {
      var rootTypeId = resolveCadenaDoTypeId(base);
      var rootDef = getDoTypeDef(rootTypeId);
      var sdoEntry = rootDef && findNamedEntry(rootDef.sdos, base.sdoName);
      if (sdoEntry) {
        var sdoDef = getDoTypeDef(sdoEntry.type);
        var daEntry = sdoDef && findNamedEntry(sdoDef.das, daName);
        if (daEntry) {
          if (isStructDaEntry(daEntry) && daEntry.type && daTypeIndex[daEntry.type]) {
            return expandCadenaTypeChildren(base, base.doName, base.sdoName, daTypeIndex[daEntry.type], [daName]);
          }
          return expandCadenaValue(base, base.doName, base.sdoName, daEntry, [], [daName]);
        }
      }
    }

    var daRow = buildCadenaDataRow(
      base,
      base.doName,
      doTypeId,
      base.sdoName || "",
      daName,
      "",
      "",
      attrs.bType || attrs.DAbType || "",
      attrs.fc || ""
    );

    if (isStructDaEntry(attrs) && attrs.type) {
      var daTypeDef = getDaTypeDef(attrs.type);
      if (daTypeDef) {
        return expandCadenaTypeChildren(
          base,
          base.doName,
          base.sdoName || "",
          daTypeDef,
          [daName]
        );
      }
    }

    return [daRow];
  }

  if (tag === "BDA_CONTENT") {
    var contentTree = window._cachedJstree || (window._cachedJstree = (window.jQuery && window.jQuery("#jstree").length ? window.jQuery("#jstree").jstree(true) : null));
    if (contentTree && nodeId) {
      var contentNode = contentTree.get_node(nodeId);
      var parentBdaNode = contentNode ? contentTree.get_node(contentNode.parent) : null;
      var parentBdaMeta = parentBdaNode && parentBdaNode.original ? parentBdaNode.original._meta : null;
      var parentBdaTag = String(parentBdaMeta && parentBdaMeta.tag ? parentBdaMeta.tag : "").toUpperCase();
      if (parentBdaMeta && (parentBdaTag === "BDA_SYNTH" || parentBdaTag === "BDA")) {
        return buildCadenaRowsFromNode(
          {
            tag: "BDA_SYNTH",
            attrs: parentBdaMeta.attrs || attrs,
            ctx: node.ctx || parentBdaMeta.ctx || {},
          },
          parentBdaNode.id
        );
      }
    }
  }

  if (tag === "BDA_SYNTH" || tag === "BDA") {
    var daAncestors = getAncestorMetasByTags(nodeId, ["DA_SYNTH", "DA"]);
    var bdaAncestors = getAncestorMetasByTags(nodeId, ["BDA_SYNTH", "BDA"]);
    var pathParts = [];
    var currentBdaName = attrs.name || attrs.daName || "";
    var nearestDaMeta = daAncestors.length ? daAncestors[daAncestors.length - 1] : null;
    var nearestDaAttrs = nearestDaMeta ? (nearestDaMeta.attrs || {}) : {};
    var daNameFromTree = nearestDaAttrs.name || nearestDaAttrs.daName || base.daName || "";

    if (daNameFromTree) pathParts.push(daNameFromTree);
    bdaAncestors.forEach(function (meta) {
      var ancestorAttrs = meta && meta.attrs ? meta.attrs : {};
      var ancestorName = ancestorAttrs.name || ancestorAttrs.daName || "";
      if (ancestorName) pathParts.push(ancestorName);
    });
    if (currentBdaName) pathParts.push(currentBdaName);

    var bdaRow = pathParts.length
      ? buildCadenaHierarchicalRow(
          base,
          base.doName,
          base.sdoName || "",
          pathParts,
          attrs.bType || attrs.DAbType || "",
          attrs.fc || ""
        )
      : buildCadenaDataRow(
          base,
          base.doName,
          doTypeId,
          base.sdoName || "",
          currentBdaName,
          "",
          "",
          attrs.bType || attrs.DAbType || "",
          attrs.fc || ""
        );

    if (isStructBdaEntry(attrs) && attrs.type) {
      var daTypeDef = getDaTypeDef(attrs.type);
      if (daTypeDef) {
        return expandCadenaTypeChildren(
          base,
          base.doName,
          base.sdoName || "",
          daTypeDef,
          pathParts.length ? pathParts : [currentBdaName]
        );
      }
    }

    return [bdaRow];
  }

  var daName = attrs.daName || attrs.name || "";
  var hierarchyFallback = (node.parentPath && String(node.parentPath).trim())
    ? node.parentPath + " / " + daName
    : daName;
  var fallbackParts = getHierarchicalNameParts(hierarchyFallback, daName);
  
  return [
    buildCadenaDataRow(
      base,
      base.doName,
      doTypeId,
      base.sdoName || "",
      fallbackParts[0] || daName,
      fallbackParts[1] || "",
      fallbackParts[2] || "",
      attrs.bType || attrs.DAbType || "",
      attrs.fc || ""
    ),
  ];
}

function collectCadenaRowsFromTreeNode(node, nodeId, rows) {
  rows = Array.isArray(rows) ? rows : [];
  if (!node || !nodeId) return rows;

    var nodeRows = buildCadenaRowsFromNode(node, nodeId);
    if (nodeRows && nodeRows.length) {
      nodeRows.forEach(function (row) {
        rows.push(row);
      });
    }

    // Si el nodo es de tipo Struct, ya se expandió recursivamente en buildCadenaRowsFromNode.
    // Detenemos la recursión por el árbol para evitar duplicados.
    var nodeTag = String(node.tag || "").toUpperCase();
    var attrs = node.attrs || {};
    if (isStructDaEntry(attrs) || isStructBdaEntry(attrs)) {
      return rows;
    }

    // DO/DO_SYNTH/DO_TYPE_CONTENT ya expanden su contenido en buildCadenaRowsFromNode.
    // Recorrer además sus hijos del árbol vuelve a leer la misma rama y duplica filas.
    if (nodeTag === "DO" || nodeTag === "DO_SYNTH" || nodeTag === "DO_TYPE_CONTENT") {
      return rows;
    }

    // Para BDA_CONTENT, DA_TYPE_CONTENT, DO, DO_SYNTH, DO_TYPE_CONTENT permitir expansión de hijos directos
    // para mostrar todos los elementos cuando el usuario selecciona el contenedor o el DO
    var allowChildExpansion = nodeTag === "BDA_CONTENT" || nodeTag === "DA_TYPE_CONTENT";

    // DA y BDA ya se expanden completamente desde su tipo; si además recorremos
    // sus hijos del árbol, terminan apareciendo filas duplicadas o desplazadas
    // donde un BDA queda ocupando la primera columna DA.
    if ([
      "DATATYPE",
      "DATYPE",
      "SDO",
      "BDA",
      "DA",
      "DA_SYNTH",
      "BDA_SYNTH",
      "SDO_SYNTH",
      "FCDA",
      "LNODETYPE",
      "LN_SYNTH"
    ].indexOf(nodeTag) >= 0 && !allowChildExpansion) {
      return rows;
    }

  var tree = window._cachedJstree || (window._cachedJstree = (window.jQuery && window.jQuery("#jstree").length ? window.jQuery("#jstree").jstree(true) : null));
  if (!tree) return rows;

  var jstreeNode = tree.get_node(nodeId);
  if (!jstreeNode || !Array.isArray(jstreeNode.children_d) || !jstreeNode.children_d.length) return rows;

  // Para BDA_CONTENT, DA_TYPE_CONTENT, DO, DO_SYNTH, DO_TYPE_CONTENT, solo procesar hijos DIRECTOS (children, no children_d)
  // para mostrar todos los elementos sin anidar muy profundo
  var childrenToProcess = jstreeNode.children || [];
  if (nodeTag !== "BDA_CONTENT" && nodeTag !== "DA_TYPE_CONTENT") {
    childrenToProcess = jstreeNode.children_d || [];
  }

  childrenToProcess.forEach(function (childId) {
    var childNode = tree.get_node(childId);
    if (!childNode || !childNode.original) return;

    var childMeta = childNode.original._meta || {};
    var childTag = String(childMeta.tag || "").toUpperCase();
    
    // Para BDA_CONTENT/DA_TYPE_CONTENT, solo incluir BDA, DA, BDA_SYNTH, DA_SYNTH hijos directos
    if ((nodeTag === "BDA_CONTENT" || nodeTag === "DA_TYPE_CONTENT") && 
        ["BDA", "DA", "BDA_SYNTH", "DA_SYNTH"].indexOf(childTag) === -1) {
      return;
    }
    
    var childParentIds = Array.isArray(childNode.parents)
      ? childNode.parents.filter(function (pid) { return pid && pid !== "#"; })
      : [];
    var childParentPath = childParentIds
      .map(function (pid) {
        var parent = tree.get_node(pid);
        return parent && parent.text ? parent.text : "";
      })
      .filter(function (part) { return Boolean(part); })
      .concat([childNode.text])
      .join(" / ");

    var storedChild = enrichStoredTreeNode(
      {
        text: childNode.text,
        tag: childMeta.tag || "",
        attrs: Object.assign({}, childMeta.attrs || {}),
        ctx: Object.assign({}, childMeta.ctx || {}),
        label: childNode.text,
        parentIds: childParentIds,
        parentPath: childParentPath,
      },
      childId
    );

    var childRows = buildCadenaRowsFromNode(storedChild, childId);
    if (childRows && childRows.length) {
      childRows.forEach(function (row) {
        rows.push(row);
      });
    }
  });

  return rows;
}

function buildCadenaIEC61850Rows(selectedIds, options) {
  options = options || {};
  var previewEntries = null;
  var dataEntries = [];
  var seen = {};
  var seenDoScopes = {};

  function pushCadenaRow(row, node, nodeId) {
    // Omitir filas que sean de tipo Struct (encabezados de contenedores)
    var bType = row[row.length - 3] || "";
    if (isStructBType(bType)) return;

    var key = cadenaRowKey(row);
    if (seen[key] || cadenaExcludedRowKeys[key]) return;
    seen[key] = true;
    dataEntries.push({ row: row, node: node || {}, nodeId: nodeId || "", key: key });
  }

  if (options.fromLnRecords && lnRecords.length && (!selectedIds || !selectedIds.length)) {
    lnRecords.forEach(function (record) {
      var base = {
        ldInst: record.LDInst || "",
        prefix: record.Prefix || "",
        lnClass: record.LNClass || "",
        lnInst: record.LNInst || "",
        doName: record.DOName || "",
      };
      var scopeKey = cadenaDoScopeKey(base, record.DOName);
      if (seenDoScopes[scopeKey]) return;
      seenDoScopes[scopeKey] = true;
      buildCadenaRowsFromLnRecord(record).forEach(function (row) {
        pushCadenaRow(row, {
          attrs: { ldDesc: record.LDDesc || "", lnDesc: record.LNDesc || "", doDesc: record.DODesc || "" },
          ctx: { ldDesc: record.LDDesc || "", lnDesc: record.LNDesc || "", desc: record.LNDesc || "", lnType: record.LNodeType || "" },
        }, "");
      });
    });
  }

  if (typeof buildCadenaPreviewEntriesOptimized === 'function') {
    previewEntries = buildCadenaPreviewEntriesOptimized(selectedIds) || [];
  }

  if (previewEntries && previewEntries.length) {
    previewEntries.forEach(function (entry) {
      var row = Array.isArray(entry && entry.row) ? entry.row : [];
      var node = entry && entry.node ? entry.node : {};
      var nodeId = entry && entry.nodeId ? entry.nodeId : '';
      pushCadenaRow(row, node, nodeId);
    });
  } else {
    (selectedIds || []).forEach(function (id) {
      var node = treeSelectedNodes[id] || {};
      var tempRows = [];
      collectCadenaRowsFromTreeNode(node, id, tempRows);
      tempRows.forEach(function (row) {
        pushCadenaRow(row, node, id);
      });
    });
  }

  var maxPathCount = Math.max(1, getCadenaMaxPathCountFromRows(dataEntries.map(function (entry) {
    return entry && entry.row ? entry.row : [];
  })));

  function normalizeCadenaEntry(entry) {
    var normalized = limitCadenaPathColumns(entry.row || [], maxPathCount);
    var descFields = getCadenaDescriptionFields(entry);
    var expectedLength = 10 + maxPathCount;
    while (normalized.length < expectedLength) {
      normalized.splice(normalized.length - 3, 0, "");
    }
    normalized.push(descFields.ldDesc || "", descFields.lnDesc || "", descFields.doDesc || "");
    return normalized;
  }

  var rows = [];
  var headerRow1 = new Array(13 + maxPathCount).fill("");
  var headerRow2 = new Array(13 + maxPathCount).fill("");

  headerRow1[1] = "LDIns";
  headerRow1[2] = "LN";
  headerRow1[5] = "DO";
  headerRow1[7] = "DA";
  headerRow1[headerRow1.length - 6] = "bType";
  headerRow1[headerRow1.length - 5] = "FC";
  headerRow1[headerRow1.length - 4] = "CADENA IEC 61850";
  headerRow1[headerRow1.length - 3] = "DESCRIPCION";

  headerRow2[2] = "Prefix";
  headerRow2[3] = "LNClass";
  headerRow2[4] = "Lninst";
  headerRow2[5] = "DoName";
  headerRow2[6] = "SDO";
  for (var i = 0; i < maxPathCount; i++) {
    headerRow2[7 + i] = i === 0 ? "DA" : (i === 1 ? "BDA" : "BDA2");
  }
  headerRow2[headerRow2.length - 3] = "LD DESC";
  headerRow2[headerRow2.length - 2] = "LN DESC";
  headerRow2[headerRow2.length - 1] = "DO DESC";

  rows.push(headerRow1);
  rows.push(headerRow2);
  dataEntries.forEach(function (entry) {
    rows.push(normalizeCadenaEntry(entry));
  });

  return rows;
}

var CADENA_DATA_START_ROW = 3;

function applyCadenaSheetStyle(sheet) {
  if (!sheet || !sheet.mergeCells) return;

  function getExcelColumnName(index) {
    var name = "";
    while (index > 0) {
      var remainder = (index - 1) % 26;
      name = String.fromCharCode(65 + remainder) + name;
      index = Math.floor((index - 1) / 26);
    }
    return name;
  }

  var colCount = sheet.columnCount || 13;
  var pathCols = Math.max(3, colCount - 13);
  var lastDataColIndex = 7 + pathCols;
  var bTypeColIndex = lastDataColIndex + 1;
  var fcColIndex = lastDataColIndex + 2;
  var resultColIndex = lastDataColIndex + 3;
  var ldDescColIndex = lastDataColIndex + 4;
  var lnDescColIndex = lastDataColIndex + 5;
  var doDescColIndex = lastDataColIndex + 6;
  var lastDataCol = getExcelColumnName(lastDataColIndex);
  var bTypeCol = getExcelColumnName(bTypeColIndex);
  var fcCol = getExcelColumnName(fcColIndex);
  var resultCol = getExcelColumnName(resultColIndex);
  var ldDescCol = getExcelColumnName(ldDescColIndex);
  var lnDescCol = getExcelColumnName(lnDescColIndex);
  var doDescCol = getExcelColumnName(doDescColIndex);

  sheet.mergeCells("B1:B2");
  sheet.mergeCells("C1:E1");
  sheet.mergeCells("F1:G1");
  sheet.mergeCells("H1:" + lastDataCol + "1");
  sheet.mergeCells(bTypeCol + "1:" + bTypeCol + "2");
  sheet.mergeCells(fcCol + "1:" + fcCol + "2");
  sheet.mergeCells(resultCol + "1:" + resultCol + "2");
  sheet.mergeCells(ldDescCol + "1:" + doDescCol + "1");

  sheet.getCell("B1").value = "LDIns";
  sheet.getCell("C1").value = "LN";
  sheet.getCell("F1").value = "DO";
  sheet.getCell("H1").value = "DA";
  sheet.getCell(bTypeCol + "1").value = "bType";
  sheet.getCell(fcCol + "1").value = "FC";
  sheet.getCell(resultCol + "1").value = "CADENA IEC 61850";
  sheet.getCell(ldDescCol + "1").value = "DESCRIPCION";
  sheet.getCell("C2").value = "Prefix";
  sheet.getCell("D2").value = "LNClass";
  sheet.getCell("E2").value = "LNInst";
  sheet.getCell("F2").value = "DO";
  sheet.getCell("G2").value = "SDO";

  for (var i = 0; i < pathCols; i++) {
    var cellAddress = getExcelColumnName(8 + i) + "2";
    sheet.getCell(cellAddress).value = i === 0 ? "DA" : (i === 1 ? "BDA" : "BDA2");
  }
  sheet.getCell(ldDescCol + "2").value = "LD DESC";
  sheet.getCell(lnDescCol + "2").value = "LN DESC";
  sheet.getCell(doDescCol + "2").value = "DO DESC";

  var headerFont = { bold: true, color: { argb: "FFFFFFFF" }, size: 11 };
  var headerAlign = { horizontal: "center", vertical: "middle", wrapText: true };

  var headerGroups = [
    ["B1", "FF059669"],
    ["C1", "FF059669"],
    ["D1", "FF059669"],
    ["E1", "FF059669"],
    ["F1", "FF059669"],
    ["G1", "FF059669"],
    ["H1", "FF059669"],
    [bTypeCol + "1", "FF059669"],
    [fcCol + "1", "FF059669"],
    [resultCol + "1", "FF059669"],
    [ldDescCol + "1", "FF059669"],
  ];
  headerGroups.forEach(function (entry) {
    var cell = sheet.getCell(entry[0]);
    cell.font = headerFont;
    cell.fill = { type: "pattern", pattern: "solid", fgColor: { argb: entry[1] } };
    cell.alignment = headerAlign;
  });

  var subHeaders = [["C2", "FF047857"], ["D2", "FF047857"], ["E2", "FF047857"], ["F2", "FF047857"], ["G2", "FF047857"], [ldDescCol + "2", "FF047857"], [lnDescCol + "2", "FF047857"], [doDescCol + "2", "FF047857"]];
  for (var j = 0; j < pathCols; j++) {
    subHeaders.push([getExcelColumnName(8 + j) + "2", "FF047857"]);
  }

  subHeaders.forEach(function (entry) {
    var subCell = sheet.getCell(entry[0]);
    subCell.font = headerFont;
    subCell.fill = { type: "pattern", pattern: "solid", fgColor: { argb: entry[1] } };
    subCell.alignment = headerAlign;
  });

  sheet.getRow(1).height = 20;
  sheet.getRow(2).height = 20;
  sheet.views = [{ state: "frozen", xSplit: 0, ySplit: 2 }];

  // Habilitar encabezado con filtro (autoFilter) sobre la fila de subencabezados (fila 2)
  // hasta la última columna de descripción, abarcando todas las filas de datos.
  var lastFilterColIndex = doDescColIndex;
  var lastFilterRow = Math.max(sheet.rowCount || 2, 2);
  sheet.autoFilter = {
    from: { row: 2, column: 1 },
    to: { row: lastFilterRow, column: lastFilterColIndex },
  };
}

function applyCadenaResultadoFormulas(sheet, dataStartRow) {
  if (!sheet) return;
  dataStartRow = dataStartRow || CADENA_DATA_START_ROW;

  function getExcelColumnName(index) {
    var name = "";
    while (index > 0) {
      var remainder = (index - 1) % 26;
      name = String.fromCharCode(65 + remainder) + name;
      index = Math.floor((index - 1) / 26);
    }
    return name;
  }

  var totalColumns = sheet.columnCount || 13;
  if (totalColumns < 11) return;
  var resultCol = getExcelColumnName(totalColumns);

  for (var r = dataStartRow; r <= sheet.rowCount; r++) {
    var ldCell = sheet.getCell("B" + r);
    if (ldCell.value === undefined || ldCell.value === null || String(ldCell.value).trim() === "") {
      continue;
    }
    var resultCell = sheet.getCell(resultCol + r);
    resultCell.value = String(resultCell.value || "");
    resultCell.numFmt = "@";
  }
}

function populateCadenaSheet(sheet, selectedIds, options) {
  var sourceRows = buildCadenaIEC61850Rows(selectedIds, options);
  var excelRows = [[], []];
  sourceRows.slice(2).forEach(function (row) {
    excelRows.push(row);
  });
  sheet.addRows(excelRows);
  applyCadenaSheetStyle(sheet);
  applyCadenaResultadoFormulas(sheet, CADENA_DATA_START_ROW);
}

function buildTreeStructureRows(selectedIds) {
  var rows = [];
  rows.push([
    "Tipo de elemento",
    "Nombre visible",
    "IED",
    "LDIns",
    "Prefix",
    "LNClass",
    "LNInst",
    "LNodeType (CID)",
    "lnClass (CID)",
    "DOName",
    "DOType",
    "DAName",
    "DAType",
    "CDC",
    "Tag",
    "CONCAT",
    "LD Desc (Logical Device Description)",
    "LN Desc (Logical Node Description)",
    "DO Desc (Data Object Description)",
    "Descripción CID",
  ]);

  var tree = window._cachedJstree || (window._cachedJstree = (window.jQuery && window.jQuery("#jstree").length ? window.jQuery("#jstree").jstree(true) : null));
  var seenNodeIds = {};

  function buildTreeStructureRow(node, nodeId) {
    if (!node) return null;
    var attrs = node.attrs || {};
    var ctx = node.ctx || {};
    var fields = resolveSelectionFields(node, nodeId);
    var cidDesc = getCidDescriptionFields(fields, attrs, ctx);
    var elementType = detectElementType(node);
    var visibleName = getReadableNodeLabel(node);
    if (!visibleName && (attrs.name || attrs.doName || attrs.daName || attrs.id || attrs.type)) {
      visibleName = [attrs.name || attrs.doName || attrs.daName || attrs.id || attrs.type, attrs.CDC || attrs.cdc].filter(Boolean).join(" | ");
    }
    var prefix = fields.prefix;
    var lnClass = fields.lnClass;
    var lnInst = fields.lnInst;
    var ldInst = fields.ldInst;
    var doName = fields.doName;
    var daName = fields.daName || attrs.daName || "";
    var hierarchySource = (node.parentPath && String(node.parentPath).trim()) ? (node.parentPath + " / " + daName) : daName;
    var daParts = getHierarchicalNameParts(hierarchySource, attrs.name || attrs.doName || attrs.daName || "");
    var concat = [prefix, lnClass, lnInst, doName, daName].filter(function (v) { return String(v || "").trim(); }).join(".");
    var parentPath = node.parentPath || "";
    var lnTypeValue = attrs["lnType (CID)"] || fields.lnType || attrs.lnType || ctx.lnType || "";
    var lnIdentifier = [prefix, lnClass, lnInst].filter(function (v) { return String(v || "").trim(); }).join("");
    var lnTypePathParts = [];
    if (ldInst) lnTypePathParts.push("LDInst: " + ldInst);
    if (lnIdentifier) lnTypePathParts.push("LN: " + lnIdentifier);
    if (lnTypeValue) lnTypePathParts.push("LNodeType: " + lnTypeValue);
    var lnTypePath = lnTypePathParts.join(" / ");
    var cidLnClass = lnTypeValue && lnodeTypeIndex[lnTypeValue] && lnodeTypeIndex[lnTypeValue].lnClass
      ? lnodeTypeIndex[lnTypeValue].lnClass
      : (attrs["lnClass (CID)"] || lnClass || "");
    var cidRouteParts = [];
    if (lnTypePath) {
      cidRouteParts.push("LNodeType: " + lnTypePath);
    }
    if (attrs.type || attrs.DOType || attrs.DAType || attrs.id) {
      var datatypeToken = attrs.DOType || attrs.DAType || attrs.type || attrs.id;
      if (datatypeToken) {
        cidRouteParts.push(String(datatypeToken) + (attrs.CDC || attrs.cdc ? " [CDC: " + (attrs.CDC || attrs.cdc) + "]" : ""));
      }
    }
    if (parentPath) {
      var normalizedParentPath = parentPath.replace(/\s*\/\s*/g, " / ");
      if (cidRouteParts.length === 0 || normalizedParentPath.indexOf(cidRouteParts[0]) === -1) {
        cidRouteParts.push(stripVisibleTypePrefixes(normalizedParentPath));
      }
    }
    var visibleNodeText = stripVisibleTypePrefixes(node.text || "");
    if (visibleNodeText && (!parentPath || parentPath.indexOf(visibleNodeText) === -1) && cidRouteParts.indexOf(visibleNodeText) === -1) {
      cidRouteParts.push(visibleNodeText);
    }
    var cidRoute = cidRouteParts.join(" / ");
    if (!cidRoute) {
      cidRoute = "LNodeType: " + (lnTypePath || "(sin LNodeType)");
    }
    cidRoute = formatNestedRoute(parentPath, cidRoute);

    var daNameValue = daParts[0] || daName || "";
    var daTypeValue = attrs.DAType || attrs.type || "";

    if (node.tag === "FCDA") {
      daNameValue = attrs.daName || daName || "";
      daTypeValue = "";
    }

    return [
      elementType,
      visibleName,
      ctx.iedName || attrs.iedName || "",
      ldInst,
      prefix,
      lnClass,
      lnInst,
      lnTypePath,
      cidLnClass,
      doName,
      attrs.DOType || attrs.type || "",
      daNameValue,
      daTypeValue,
      attrs.CDC || attrs.cdc || "",
      node.tag || "",
      concat,
      cidDesc.ldDesc || "",
      cidDesc.lnDesc || "",
      cidDesc.doDesc || "",
      buildSelectionCidDescription(node, fields, attrs, ctx),
    ];
  }

  function collectNodeAndDescendants(nodeId) {
    if (!tree || !nodeId || seenNodeIds[nodeId]) return;
    var jstreeNode = tree.get_node(nodeId);
    if (!jstreeNode || !jstreeNode.original || !jstreeNode.original._meta) return;
    seenNodeIds[nodeId] = true;

    var childMeta = jstreeNode.original._meta || {};
    var childParentIds = Array.isArray(jstreeNode.parents)
      ? jstreeNode.parents.filter(function (pid) { return pid && pid !== "#"; })
      : [];
    var childParentPath = childParentIds
      .map(function (pid) {
        var parent = tree.get_node(pid);
        return parent && parent.text ? parent.text : "";
      })
      .filter(function (part) { return Boolean(part); })
      .concat([jstreeNode.text])
      .join(" / ");

    var storedNode = enrichStoredTreeNode(
      {
        text: jstreeNode.text,
        tag: childMeta.tag || "",
        attrs: Object.assign({}, childMeta.attrs || {}),
        ctx: Object.assign({}, childMeta.ctx || {}),
        label: jstreeNode.text,
        parentIds: childParentIds,
        parentPath: childParentPath,
      },
      nodeId
    );

    var row = buildTreeStructureRow(storedNode, nodeId);
    if (row) rows.push(row);

    (jstreeNode.children_d || []).forEach(function (childId) {
      collectNodeAndDescendants(childId);
    });
  }

  selectedIds.forEach(function (id) {
    collectNodeAndDescendants(id);
  });

  return rows;
}

function downloadTreeSelectionAsExcel() {
  var selectedIds = sortTreeSelectedIds(getSelectedTreeIds());
  if (!selectedIds.length) {
    alert("Selecciona al menos un elemento del árbol para descargar.");
    return;
  }

  setStatus("Generando descarga de elementos seleccionados del árbol...");
  if (typeof ExcelJS === "undefined" || !ExcelJS.Workbook) {
    setStatus("ExcelJS no disponible: exportando árbol seleccionado con formato básico...");
    return exportTreeSelectionFallback(selectedIds);
  }

  try {
    var workbook = new ExcelJS.Workbook();
    workbook.creator = "CID Tool";
    workbook.created = new Date();

    var cadenaSheet = workbook.addWorksheet("CADENA");
    populateCadenaSheet(cadenaSheet, selectedIds);
    applyExcelAutoFit(cadenaSheet, 10);
    applyExcelFrame(cadenaSheet, "FF334155");

    appendTreeSelectionMetaSheetExcelJS(workbook);
    workbook.views = [{ activeTab: 0 }];

    workbook.xlsx.writeBuffer().then(function (buffer) {
      try {
        var excelBlob = new Blob([buffer], { type: "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet" });
        saveBlobAs(excelBlob, getCadenaExportFileName());
        setStatus("✓ Descarga completada. " + selectedIds.length + " elementos exportados.");
      } catch (e2) {
        saveBlobAs(new Blob([buffer], { type: "application/octet-stream" }), getCadenaExportFileName());
        setStatus("✓ Descarga completada. " + selectedIds.length + " elementos exportados.");
      }
    }).catch(function (err) {
      setStatus("Error al generar el Excel: " + (err && err.message ? err.message : err));
      console.error(err);
    });
  } catch (ex) {
    setStatus("Error: " + ex.message);
    console.error(ex);
  }
}

function exportTreeSelectionFallback(selectedIds) {
  selectedIds = sortTreeSelectedIds(selectedIds && selectedIds.length ? selectedIds : getSelectedTreeIds());

  var wb = XLSX.utils.book_new();
  var cadenaRows = buildCadenaIEC61850Rows(selectedIds).slice(1);
  var ws2 = XLSX.utils.aoa_to_sheet(cadenaRows);
  // Habilitar encabezado con filtro en la hoja CADENA (fila de subencabezados).
  if (cadenaRows.length) {
    var cadenaColCount = (cadenaRows[0] || []).length || 13;
    var cadenaLastRow = Math.max(cadenaRows.length, 1);
    ws2["!autofilter"] = {
      ref: XLSX.utils.encode_range(
        { r: 0, c: 0 },
        { r: cadenaLastRow - 1, c: cadenaColCount - 1 }
      ),
    };
  }
  XLSX.utils.book_append_sheet(wb, ws2, "CADENA");
  appendTreeSelectionMetaSheetSheetJS(wb);
  wb.Workbook = wb.Workbook || {};
  wb.Workbook.Views = [{ ActiveTab: 0 }];
  downloadWB(wb, getCadenaExportFileName());

  setStatus("✓ Descarga completada. " + selectedIds.length + " elementos exportados.");
}

// Recursive navigation function for DO → DOType → SDO → DA → DAType → BDA relationships
function traverseDoRecursively(lnTypeId, doName, level, path, results) {
  level = level || 0;
  path = path || "";
  results = results || [];

  var lnt = lnodeTypeIndex[lnTypeId];
  if (!lnt) return results;

  var doEntry = lnt.dos.find(function (d) { return d.name === doName; });
  if (!doEntry) return results;

  var doTypeDef = getDoTypeDef(doEntry.type);
  var currentPath = path ? path + "/" + doName : doName;

  // Add DO row
  results.push({
    level: level,
    lnodeType: lnTypeId,
    do: doName,
    sdo: "",
    da: "",
    bda: "",
    fc: "",
    bType: "",
    type: doEntry.type,
    relatedId: doEntry.type,
    description: doTypeDef ? (doTypeDef.cdc || "") : "",
    path: currentPath,
    element: "DO"
  });

  if (!doTypeDef) return results;

  // Process SDOs recursively
  if (doTypeDef.sdos && doTypeDef.sdos.length) {
    doTypeDef.sdos.forEach(function (sdo) {
      var sdoPath = currentPath + "/" + sdo.name;
      results.push({
        level: level + 1,
        lnodeType: lnTypeId,
        do: doName,
        sdo: sdo.name,
        da: "",
        bda: "",
    
        bType: "",
        type: sdo.type,
        relatedId: sdo.type,
        description: "",
        path: sdoPath,
        element: "SDO"
      });

      // Recursively traverse SDO's DOType
      if (sdo.type) {
        traverseSdoRecursively(sdo.type, level + 2, sdoPath, results, lnTypeId, doName, sdo.name);
      }
    });
  }

  // Process DAs
  if (doTypeDef.das && doTypeDef.das.length) {
    doTypeDef.das.forEach(function (da) {
      var daPath = currentPath + "/" + da.name;
      results.push({
        level: level + 1,
        lnodeType: lnTypeId,
        do: doName,
        sdo: "",
        da: da.name,
        bda: "",
       
        bType: da.bType || "",
        type: da.type || "",
        relatedId: da.type || "",
        description: da.attrs && da.attrs.desc ? da.attrs.desc : "",
        path: daPath,
        element: "DA"
      });

      // Solo bType="Struct" referencia DAType y debe expandir BDA.
      if (da.type && isStructDaEntry(da)) {
        traverseDaTypeRecursively(da.type, level + 2, daPath, results, lnTypeId, doName, "", da.name);
      }
    });
  }

  return results;
}

// Recursive function for SDO → DOType → SDO/DA
function traverseSdoRecursively(doTypeId, level, path, results, lnTypeId, parentDo, parentSdo) {
  var doTypeDef = getDoTypeDef(doTypeId);
  if (!doTypeDef) return results;

  // Process SDOs recursively
  if (doTypeDef.sdos && doTypeDef.sdos.length) {
    doTypeDef.sdos.forEach(function (sdo) {
      var sdoPath = path + "/" + sdo.name;
      results.push({
        level: level,
        lnodeType: lnTypeId,
        do: parentDo,
        sdo: parentSdo + "/" + sdo.name,
        da: "",
        bda: "",
        fc: "",
        bType: "",
        type: sdo.type,
        relatedId: sdo.type,
        description: "",
        path: sdoPath,
        element: "SDO"
      });

      // Recursively traverse SDO's DOType
      if (sdo.type) {
        traverseSdoRecursively(sdo.type, level + 1, sdoPath, results, lnTypeId, parentDo, parentSdo + "/" + sdo.name);
      }
    });
  }

  // Process DAs
  if (doTypeDef.das && doTypeDef.das.length) {
    doTypeDef.das.forEach(function (da) {
      var daPath = path + "/" + da.name;
      results.push({
        level: level,
        lnodeType: lnTypeId,
        do: parentDo,
        sdo: parentSdo,
        da: da.name,
        bda: "",
        fc: da.fc || "",
        bType: da.bType || "",
        type: da.type || "",
        relatedId: da.type || "",
        description: da.attrs && da.attrs.desc ? da.attrs.desc : "",
        path: daPath,
        element: "DA"
      });

      // Solo bType="Struct" referencia DAType y debe expandir BDA.
      if (da.type && isStructDaEntry(da)) {
        traverseDaTypeRecursively(da.type, level + 1, daPath, results, lnTypeId, parentDo, parentSdo, da.name);
      }
    });
  }
}

// Recursive function for DAType → BDA
function traverseDaTypeRecursively(daTypeId, level, path, results, lnTypeId, parentDo, parentSdo, parentDa) {
  var daTypeDef = daTypeIndex[daTypeId];
  if (!daTypeDef) return results;

  if (daTypeDef.bdas && daTypeDef.bdas.length) {
    daTypeDef.bdas.forEach(function (bda) {
      var bdaPath = path + "/" + bda.name;
      results.push({
        level: level,
        lnodeType: lnTypeId,
        do: parentDo,
        sdo: parentSdo,
        da: parentDa,
        bda: bda.name,
        fc: bda.fc || "",
        bType: bda.bType || "",
        type: bda.type || "",
        relatedId: bda.type || "",
        description: bda.attrs && bda.attrs.desc ? bda.attrs.desc : "",
        path: bdaPath,
        element: "BDA"
      });

      // Solo bType="Struct" anida otro DAType.
      if (bda.type && isStructBdaEntry(bda)) {
        traverseDaTypeRecursively(bda.type, level + 1, bdaPath, results, lnTypeId, parentDo, parentSdo, parentDa + "/" + bda.name);
      }
    });
  }
}

// Main function to trigger recursive navigation when clicking on a DO
function navigateDoRecursively(lnTypeId, doName) {
  var results = traverseDoRecursively(lnTypeId, doName);
  displayHierarchicalNavigation(results);
}

// Display hierarchical navigation results in a table
function displayHierarchicalNavigation(results) {
  var container = document.getElementById("hierarchical-nav-container");
  if (!container) return;

  if (!results || results.length === 0) {
    container.innerHTML = '<div style="color: #64748b; text-align: center; padding: 20px;">No se encontraron resultados</div>';
    return;
  }

  // Store results for export
  window.currentHierarchicalResults = results;

  var html = '<table style="width: 100%; border-collapse: collapse; font-size: 12px;">';
  html += '<thead><tr style="background: #1e4d8c; color: white;">';
  html += '<th style="padding: 8px; border: 1px solid #334155;">Nivel</th>';
  html += '<th style="padding: 8px; border: 1px solid #334155;">LNodeType</th>';
  html += '<th style="padding: 8px; border: 1px solid #334155;">DO</th>';
  html += '<th style="padding: 8px; border: 1px solid #334155;">SDO</th>';
  html += '<th style="padding: 8px; border: 1px solid #334155;">DA</th>';
  html += '<th style="padding: 8px; border: 1px solid #334155;">BDA</th>';
  html += '<th style="padding: 8px; border: 1px solid #334155;">FC</th>';
  html += '<th style="padding: 8px; border: 1px solid #334155;">BType</th>';
  html += '<th style="padding: 8px; border: 1px solid #334155;">Type</th>';
  html += '<th style="padding: 8px; border: 1px solid #334155;">Id Relacionado</th>';
  html += '<th style="padding: 8px; border: 1px solid #334155;">Descripción</th>';
  html += '<th style="padding: 8px; border: 1px solid #334155;">Ruta</th>';
  html += '</tr></thead><tbody>';

  results.forEach(function (row) {
    var indent = '&nbsp;&nbsp;&nbsp;&nbsp;'.repeat(row.level);
    var bgColor = row.level % 2 === 0 ? '#0f172a' : '#1e293b';
    html += '<tr style="background: ' + bgColor + ';">';
    html += '<td style="padding: 6px; border: 1px solid #334155; color: #cbd5e1;">' + row.level + '</td>';
    html += '<td style="padding: 6px; border: 1px solid #334155; color: #93c5fd;">' + esc(row.lnodeType) + '</td>';
    html += '<td style="padding: 6px; border: 1px solid #334155; color: #e2e8f0;">' + indent + esc(row.do) + '</td>';
    html += '<td style="padding: 6px; border: 1px solid #334155; color: #a5b4fc;">' + esc(row.sdo) + '</td>';
    html += '<td style="padding: 6px; border: 1px solid #334155; color: #fcd34d;">' + esc(row.da) + '</td>';
    html += '<td style="padding: 6px; border: 1px solid #334155; color: #86efac;">' + esc(row.bda) + '</td>';
    html += '<td style="padding: 6px; border: 1px solid #334155; color: #f472b6;">' + esc(row.fc) + '</td>';
    html += '<td style="padding: 6px; border: 1px solid #334155; color: #c4b5fd;">' + esc(row.bType) + '</td>';
    html += '<td style="padding: 6px; border: 1px solid #334155; color: #60a5fa;">' + esc(row.type) + '</td>';
    html += '<td style="padding: 6px; border: 1px solid #334155; color: #34d399;">' + esc(row.relatedId) + '</td>';
    html += '<td style="padding: 6px; border: 1px solid #334155; color: #e2e8f0;">' + esc(row.description) + '</td>';
    html += '<td style="padding: 6px; border: 1px solid #334155; color: #fbbf24; font-family: monospace;">' + esc(row.path) + '</td>';
    html += '</tr>';
  });

  html += '</tbody></table>';
  container.innerHTML = html;
}

// Export hierarchical navigation results to Excel
function exportHierarchicalNavigationToExcel() {
  var results = window.currentHierarchicalResults;
  if (!results || results.length === 0) {
    setStatus("No hay resultados para exportar");
    return;
  }

  try {
    var workbook = new ExcelJS.Workbook();
    var worksheet = workbook.addWorksheet("Navegación Jerárquica");

    // Add header row
    worksheet.addRow(["Nivel", "LNodeType", "DO", "SDO", "DA", "BDA", "FC", "BType", "Type", "Id Relacionado", "Descripción", "Ruta"]);

    // Style header row
    var headerRow = worksheet.getRow(1);
    headerRow.font = { bold: true, color: { argb: "FFFFFFFF" } };
    headerRow.fill = { type: "pattern", pattern: "solid", fgColor: { argb: "FF1E4D8C" } };
    headerRow.alignment = { horizontal: "center", vertical: "middle" };
    headerRow.height = 25;

    // Add data rows
    results.forEach(function (row) {
      var indent = "  ".repeat(row.level);
      worksheet.addRow([
        row.level,
        row.lnodeType,
        indent + row.do,
        row.sdo,
        row.da,
        row.bda,
        row.fc,
        row.bType,
        row.type,
        row.relatedId,
        row.description,
        row.path
      ]);
    });

    // Auto-fit columns
    applyExcelAutoFit(worksheet, 12);
    applyExcelFrame(worksheet, "FF334155");

    // Freeze header row
    worksheet.views = [{ state: "frozen", ySplit: 1 }];

    // Export
    workbook.xlsx.writeBuffer().then(function (buffer) {
      var excelBlob = new Blob([buffer], { type: "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet" });
      saveBlobAs(excelBlob, "Navegacion_Jerarquica_Recursiva.xlsx");
      setStatus("✓ Exportación completada. " + results.length + " elementos exportados.");
    });
  } catch (ex) {
    setStatus("Error al exportar: " + ex.message);
    console.error(ex);
  }
}