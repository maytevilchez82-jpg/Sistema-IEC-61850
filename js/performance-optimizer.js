// ═══════════════════════════════════════════════════════════════════════════════
// PERFORMANCE OPTIMIZER - Optimizaciones de rendimiento para árbol y tabla
// ═══════════════════════════════════════════════════════════════════════════════

/**
 * Cache para resultados de buildCadenaPreviewEntries
 * Se invalida solo cuando los nodos seleccionados cambian
 */
var cadenaEntriesCache = {
  entries: [],
  lastSelectedIds: {},
  isValid: function(selectedIds) {
    var currentKeys = (selectedIds || []).sort().join('|');
    var cachedKeys = Object.keys(this.lastSelectedIds).sort().join('|');
    return currentKeys === cachedKeys;
  },
  set: function(selectedIds, entries) {
    this.entries = entries;
    this.lastSelectedIds = {};
    (selectedIds || []).forEach(function(id) {
      this.lastSelectedIds[id] = true;
    }, this);
  },
  get: function() {
    return this.entries.slice();
  },
  clear: function() {
    this.entries = [];
    this.lastSelectedIds = {};
  }
};

function getCadenaExcludedRowCount(key) {
  var value = cadenaExcludedRowKeys && cadenaExcludedRowKeys[key];
  if (!value) return 0;
  if (value === true) return 1;
  var count = parseInt(value, 10);
  return isNaN(count) || count < 1 ? 0 : count;
}

function incrementCadenaExcludedRowCount(key) {
  if (!key) return;
  var nextCount = getCadenaExcludedRowCount(key) + 1;
  cadenaExcludedRowKeys[key] = nextCount;
}

function clearCadenaExcludedRowCount(key) {
  if (!key || !cadenaExcludedRowKeys) return;
  delete cadenaExcludedRowKeys[key];
}

/**
 * Debounce mejorado con requestIdleCallback para no bloquear la UI
 */
var updateDisplayTimer = null;
var updateDisplayIdleHandle = null;
var pendingUpdateDisplayCall = false;
var cadenaPreviewHiddenEntryIds = {};
var cadenaPreviewHiddenSelectionSignature = "";
var cadenaPreviewRemovedEntryIds = {};
var cadenaPreviewRemovedRowKeys = {};

function getCadenaSelectionSignature(selectedIds) {
  return (selectedIds || []).slice().sort().join("|");
}

function syncCadenaPreviewHiddenEntryIds(selectedIds) {
  var signature = getCadenaSelectionSignature(selectedIds);
  if (signature !== cadenaPreviewHiddenSelectionSignature) {
    cadenaPreviewHiddenSelectionSignature = signature;
    cadenaPreviewHiddenEntryIds = {};
  }
}

function hideCadenaPreviewEntry(entryId) {
  if (!entryId) return;
  cadenaPreviewHiddenEntryIds[entryId] = true;
  // Invalidar caché para que la fila eliminada no reaparezca en la siguiente renderización
  if (cadenaEntriesCache && typeof cadenaEntriesCache.clear === "function") {
    cadenaEntriesCache.clear();
  }
}

function hideCadenaPreviewRow(entryId, rowKey) {
  if (entryId) cadenaPreviewRemovedEntryIds[entryId] = true;
  if (rowKey) cadenaPreviewRemovedRowKeys[rowKey] = true;
  if (entryId) hideCadenaPreviewEntry(entryId);
  if (cadenaEntriesCache && typeof cadenaEntriesCache.clear === "function") {
    cadenaEntriesCache.clear();
  }
}

function clearCadenaPreviewRemovedRowsForNode(nodeId, rows) {
  (rows || []).forEach(function (row) {
    var rowKey = typeof cadenaRowKey === "function" ? cadenaRowKey(row) : "";
    if (!rowKey) return;
    delete cadenaPreviewRemovedRowKeys[rowKey];
    if (nodeId) {
      var prefix = nodeId + "||" + rowKey + "||";
      Object.keys(cadenaPreviewRemovedEntryIds || {}).forEach(function (entryId) {
        if (String(entryId || "").indexOf(prefix) === 0) {
          delete cadenaPreviewRemovedEntryIds[entryId];
        }
      });
    }
  });
}

function clearCadenaPreviewHiddenEntriesForNode(nodeId, rows) {
  if (!nodeId || !Array.isArray(rows) || !rows.length) return;

  rows.forEach(function (row) {
    var rowKey = typeof cadenaRowKey === "function" ? cadenaRowKey(row) : "";
    if (!rowKey) return;

    var prefix = nodeId + "||" + rowKey + "||";
    Object.keys(cadenaPreviewHiddenEntryIds || {}).forEach(function (entryId) {
      if (String(entryId || "").indexOf(prefix) === 0) {
        delete cadenaPreviewHiddenEntryIds[entryId];
      }
    });
  });
}

function clearCadenaPreviewRemovedRows() {
  cadenaPreviewRemovedEntryIds = {};
  cadenaPreviewRemovedRowKeys = {};
}

function clearCadenaPreviewHiddenEntries() {
  cadenaPreviewHiddenEntryIds = {};
  cadenaPreviewHiddenSelectionSignature = "";
  clearCadenaPreviewRemovedRows();
  if (cadenaEntriesCache && typeof cadenaEntriesCache.clear === "function") {
    cadenaEntriesCache.clear();
  }
}

function scheduleUpdateTreeSelectionDisplay() {
  // Si ya hay una actualización programada, no hacer nada
  if (pendingUpdateDisplayCall) return;
  
  pendingUpdateDisplayCall = true;
  
  // Cancelar timer anterior
  if (updateDisplayTimer) clearTimeout(updateDisplayTimer);
  if (updateDisplayIdleHandle) cancelIdleCallback(updateDisplayIdleHandle);
  
  // Esperar 150ms para agrupar múltiples cambios rápidos
  updateDisplayTimer = setTimeout(function() {
    updateDisplayTimer = null;
    
    // Usar requestIdleCallback si está disponible para no bloquear
    if (window.requestIdleCallback) {
      updateDisplayIdleHandle = requestIdleCallback(function() {
        pendingUpdateDisplayCall = false;
        updateDisplayIdleHandle = null;
        updateTreeSelectionDisplay();
      }, { timeout: 300 });
    } else {
      // Fallback: usar requestAnimationFrame
      requestAnimationFrame(function() {
        pendingUpdateDisplayCall = false;
        updateTreeSelectionDisplay();
      });
    }
  }, 150);
}

/**
 * Versión optimizada de buildCadenaPreviewEntries con caché
 */
function buildCadenaPreviewEntriesOptimized(selectedIds) {
  // Si el caché es válido, devolverlo
  if (cadenaEntriesCache.isValid(selectedIds)) {
    return cadenaEntriesCache.get();
  }

  syncCadenaPreviewHiddenEntryIds(selectedIds);

  var selectedIdSet = {};
  (selectedIds || []).forEach(function (id) {
    if (id) selectedIdSet[id] = true;
  });

  function isCoveredBySelectedAncestor(nodeId) {
    var node = treeSelectedNodes && treeSelectedNodes[nodeId] ? treeSelectedNodes[nodeId] : null;
    var parentIds = node && Array.isArray(node.parentIds) ? node.parentIds : [];
    for (var i = 0; i < parentIds.length; i++) {
      var parentId = parentIds[i];
      if (!parentId || !selectedIdSet[parentId]) continue;
      var parentNode = treeSelectedNodes[parentId] || {};
      var parentTag = String(parentNode.tag || "").toUpperCase();
      if (
        parentTag === "LN_SYNTH" || parentTag === "LN" || parentTag === "LN0" || parentTag === "LNODETYPE" ||
        parentTag === "DO" || parentTag === "DO_SYNTH" || parentTag === "DO_TYPE_CONTENT"
      ) {
        return true;
      }
    }
    return false;
  }
  
  var entries = [];
  var seenEntryKeys = {};
  var seenRowKeys = {};
  var seenDisplayRowKeys = {};
  var seenUniqueIdentifiers = {};
  var consumedExcludedKeys = {};
  var pendingItems = [];
  var entrySequenceByKey = {};

  (selectedIds || []).forEach(function (id) {
    var node = treeSelectedNodes[id] || {};
    if (isCoveredBySelectedAncestor(id)) return;
    var rows = [];
    collectCadenaRowsFromTreeNode(node, id, rows);
    rows.forEach(function (row) {
      if (isStructBType(row[row.length - 3] || "")) return;
      pendingItems.push({ id: id, node: node, row: row });
    });
  });

  var maxPathCount = typeof getCadenaMaxPathCountFromRows === 'function'
    ? getCadenaMaxPathCountFromRows(pendingItems.map(function (item) { return item.row; }))
    : 3;

  pendingItems.forEach(function (item) {
    var id = item.id;
    var node = item.node;
    var row = item.row;
    var normalizedRow = typeof limitCadenaPathColumns === 'function'
      ? limitCadenaPathColumns(row, maxPathCount)
      : row;

    var bType = normalizedRow[normalizedRow.length - 3] || "";
    var rowKey = cadenaRowKey(normalizedRow);
    var entryKey = id + "||" + rowKey;

    var allowDuplicateRowsForNode = false;
    var nodeTagUpper = String((node && node.tag) || "").toUpperCase();
    var rootTag = nodeTagUpper;
    if (
      nodeTagUpper === "BDA" || nodeTagUpper === "BDA_SYNTH" || nodeTagUpper === "BDA_CONTENT" ||
      nodeTagUpper === "SDO" || nodeTagUpper === "SDO_SYNTH"
    ) {
      allowDuplicateRowsForNode = true;
    }

    var uniqueIdentifier = normalizedRow
      .slice(1, normalizedRow.length - 1)
      .map(function (value) {
        return value == null ? "" : String(value);
      })
      .join("||");

    var excludedEntryCount = getCadenaExcludedRowCount(entryKey);
    var consumedEntryCount = consumedExcludedKeys[entryKey] || 0;
    if (consumedEntryCount < excludedEntryCount) {
      consumedExcludedKeys[entryKey] = consumedEntryCount + 1;
      return;
    }

    if (seenDisplayRowKeys[rowKey]) return;

    var occurrenceIndex = (entrySequenceByKey[entryKey] || 0) + 1;
    entrySequenceByKey[entryKey] = occurrenceIndex;
    var entryId = entryKey + "||" + occurrenceIndex;
    if (cadenaPreviewHiddenEntryIds[entryId] || cadenaPreviewRemovedEntryIds[entryId] || cadenaPreviewRemovedRowKeys[rowKey]) return;

    if (seenEntryKeys[entryKey]) return;

    if (!allowDuplicateRowsForNode) {
      if (seenRowKeys[rowKey] || seenUniqueIdentifiers[uniqueIdentifier]) return;
      seenRowKeys[rowKey] = true;
      seenUniqueIdentifiers[uniqueIdentifier] = true;
    }

    seenEntryKeys[entryKey] = true;
    seenDisplayRowKeys[rowKey] = true;
    entries.push({ row: row, nodeId: id, node: node, matched: false, key: entryKey, rowKey: rowKey, entryId: entryId, rootTag: rootTag });
  });

  // Guardar en caché
  cadenaEntriesCache.set(selectedIds, entries);
  return entries;
}

/**
 * Limpia el caché cuando se carga un archivo nuevo
 */
function clearCadenaEntriesCache() {
  cadenaEntriesCache.clear();
}
