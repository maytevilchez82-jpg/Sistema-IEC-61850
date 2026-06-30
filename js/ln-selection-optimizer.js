(function (root) {
  var selectionRunToken = 0;
  var currentSelectionState = null;

  function scheduleWork(callback) {
    if (root.requestIdleCallback) {
      return root.requestIdleCallback(callback, { timeout: 180 });
    }

    return root.requestAnimationFrame(function () {
      callback({
        timeRemaining: function () {
          return 8;
        },
      });
    });
  }

  function normalizeTag(value) {
    return String(value || "").toUpperCase();
  }

  function storeNode(tree, node, nodeId, tag, attrs, ctx, parentIds, parentPath) {
    if (!node || !nodeId) return;

    var stored = {
      text: node.text,
      tag: tag,
      attrs: Object.assign({}, attrs || {}),
      ctx: Object.assign({}, ctx || {}),
      label: node.text,
      parentIds: Array.isArray(parentIds) ? parentIds.slice() : [],
      parentPath: parentPath || node.text || "",
    };

    if (typeof root.enrichStoredTreeNode === "function") {
      stored = root.enrichStoredTreeNode(stored, nodeId);
    }

    root.treeSelectedNodes = root.treeSelectedNodes || {};
    root.treeSelectedOrder = Array.isArray(root.treeSelectedOrder) ? root.treeSelectedOrder : [];
    root.treeSelectedNodes[nodeId] = stored;
    if (root.treeSelectedOrder.indexOf(nodeId) === -1) root.treeSelectedOrder.push(nodeId);
  }

  function setTreeCheckState(tree, node, checked) {
    if (!tree || !node || typeof tree.check_node !== "function") return;

    var previous = root._suppressTreeSync;
    root._suppressTreeSync = true;
    try {
      if (checked) {
        tree.check_node(node);
      } else if (typeof tree.uncheck_node === "function") {
        tree.uncheck_node(node);
      }
    } catch (e) {
    } finally {
      root._suppressTreeSync = previous;
    }
  }

  function buildParentPath(tree, node) {
    var parentIds = Array.isArray(node && node.parents)
      ? node.parents.filter(function (pid) {
          return pid && pid !== "#";
        })
      : [];

    var parentPath = parentIds
      .map(function (pid) {
        var parentNode = tree.get_node(pid);
        return parentNode && parentNode.text ? parentNode.text : "";
      })
      .filter(Boolean)
      .concat([node.text])
      .join(" / ");

    return {
      parentIds: parentIds,
      parentPath: parentPath,
    };
  }

  function queueLnDescendants(tree, node) {
    if (!tree || !node) return [];
    if (Array.isArray(node.children_d) && node.children_d.length) return node.children_d.slice();
    if (Array.isArray(node.children) && node.children.length) return node.children.slice();
    return [];
  }

  function finalizeSelection() {
    if (currentSelectionState) currentSelectionState.done = true;

    if (typeof root.pruneCadenaExcludedRows === "function" && typeof root.getSelectedTreeIds === "function") {
      root.pruneCadenaExcludedRows(root.getSelectedTreeIds());
    }

    if (typeof root.scheduleUpdateTreeSelectionDisplay === "function") {
      root.scheduleUpdateTreeSelectionDisplay();
    } else if (typeof root.updateTreeSelectionDisplay === "function") {
      root.updateTreeSelectionDisplay();
    }

    if (typeof root.switchTab === "function") root.switchTab("excel");
    if (typeof root.setStatus === "function") root.setStatus("Se seleccionaron todos los DO del nodo.");
  }

  function processSelectionChunk(state, deadline) {
    if (!state || state.done) return;
    if (state.token !== selectionRunToken) return;

    var processed = 0;
    while (state.index < state.descendantIds.length && processed < state.chunkSize) {
      if (deadline && typeof deadline.timeRemaining === "function" && deadline.timeRemaining() <= 4) break;

      var childId = state.descendantIds[state.index++];
      var childNode = state.tree.get_node(childId);
      if (!childNode || !childNode.original || !childNode.original._meta) {
        processed++;
        continue;
      }

      var childTag = normalizeTag(childNode.original._meta.tag || "");
      if (childTag !== "DO" && childTag !== "DO_SYNTH") {
        processed++;
        continue;
      }

      var childContext = buildParentPath(state.tree, childNode);
      storeNode(
        state.tree,
        childNode,
        childNode.id,
        childTag,
        childNode.original._meta.attrs || {},
        childNode.original._meta.ctx || {},
        childContext.parentIds,
        childContext.parentPath
      );
      processed++;
    }

    if (state.token !== selectionRunToken || state.done) return;

    if (state.index < state.descendantIds.length) {
      scheduleWork(function (nextDeadline) {
        processSelectionChunk(state, nextDeadline);
      });
      return;
    }

    finalizeSelection();
    if (currentSelectionState === state) currentSelectionState = null;
  }

  function enqueueOptimizedLnSelection(tree, node, nodeId, nodeTag, nodeAttrs, nodeCtx, parentIds, parentPath) {
    if (!tree || !node || !nodeId) return false;

    if (currentSelectionState && currentSelectionState.nodeId === nodeId && !currentSelectionState.done) {
      processSelectionChunk(currentSelectionState, {
        timeRemaining: function () {
          return 12;
        },
      });
      return true;
    }

    var runToken = ++selectionRunToken;
    var resolvedTag = normalizeTag(nodeTag);
    var resolvedAttrs = Object.assign({}, nodeAttrs || {});
    var resolvedCtx = Object.assign({}, nodeCtx || {});
    var resolvedParents = Array.isArray(parentIds) ? parentIds.slice() : [];
    var resolvedPath = parentPath || node.text || "";

    if (typeof tree.open_node === "function") {
      try {
        tree.open_node(node);
      } catch (e) {}
    }

    storeNode(tree, node, nodeId, resolvedTag, resolvedAttrs, resolvedCtx, resolvedParents, resolvedPath);

    if (typeof root.applyTreeCheckedHighlights === "function") {
      if (root.requestAnimationFrame) {
        root.requestAnimationFrame(function () {
          root.applyTreeCheckedHighlights(tree);
        });
      } else {
        setTimeout(function () {
          root.applyTreeCheckedHighlights(tree);
        }, 0);
      }
    }

    var descendantIds = queueLnDescendants(tree, node);
    currentSelectionState = {
      token: runToken,
      nodeId: nodeId,
      tree: tree,
      descendantIds: descendantIds,
      index: 0,
      chunkSize: 60,
      done: false,
    };

    if (!descendantIds.length) {
      finalizeSelection();
      currentSelectionState = null;
      return true;
    }

    scheduleWork(function (deadline) {
      processSelectionChunk(currentSelectionState, deadline);
    });
    return true;
  }

  root.enqueueOptimizedLnSelection = enqueueOptimizedLnSelection;
})(window);
