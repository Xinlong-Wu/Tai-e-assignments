/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;
import polyglot.ast.Assign;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (callGraph.addReachableMethod(method)) {
            for (var stmt: method.getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        public Void visit(New newStmt) {
            VarPtr ptr = pointerFlowGraph.getVarPtr(newStmt.getLValue());
//            if (ptr.getPointsToSet().isEmpty()){
                Obj obj = heapModel.getObj(newStmt);
                workList.addEntry(ptr, new PointsToSet(obj));
//            }
            return null;
        }

        public Void visit(Copy copyStmt) {
            VarPtr dst = pointerFlowGraph.getVarPtr(copyStmt.getLValue());
            VarPtr src = pointerFlowGraph.getVarPtr(copyStmt.getRValue());
            addPFGEdge(src, dst);
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                var src = pointerFlowGraph.getVarPtr(stmt.getRValue());
                var dst = pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(src, dst);
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                var src = pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
                var dst = pointerFlowGraph.getVarPtr(stmt.getLValue());

                addPFGEdge(src, dst);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                var method = resolveCallee(null, stmt);

                Edge<Invoke, JMethod> edge = new Edge<>(CallKind.STATIC, stmt, method);
                if (callGraph.addEdge(edge)) {
                    doProcessCall(stmt, method);
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            var pt = source.getPointsToSet();
            if (!pt.isEmpty()) {
                workList.addEntry(target, pt);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            var entry = workList.pollEntry();
            var delta = propagate(entry.pointer(), entry.pointsToSet());
            if (entry.pointer() instanceof VarPtr ptr) {
                Var var = ptr.getVar();
                for(var obj: delta) {
                    for (var storeField: var.getStoreFields()) {
                        var src = pointerFlowGraph.getVarPtr(storeField.getRValue());
                        var dst = pointerFlowGraph.getInstanceField(obj, storeField.getFieldRef().resolve());
                        addPFGEdge(src, dst);
                    }

                    for(var loadField: var.getLoadFields()) {
                        var src = pointerFlowGraph.getInstanceField(obj, loadField.getFieldRef().resolve());
                        var dst = pointerFlowGraph.getVarPtr(loadField.getLValue());
                        addPFGEdge(src, dst);
                    }

                    for (var arrStore: var.getStoreArrays()) {
                        var src = pointerFlowGraph.getVarPtr(arrStore.getRValue());
                        var idx = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(src, idx);
                    }

                    for (var arrLoad: var.getLoadArrays()) {
                        var src = pointerFlowGraph.getArrayIndex(obj);
                        var dst = pointerFlowGraph.getVarPtr(arrLoad.getLValue());
                        addPFGEdge(src, dst);
                    }

                    processCall(var, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet difference = new PointsToSet();
        PointsToSet ptn = pointer.getPointsToSet();
        for (Obj obj : pointsToSet) {
            if (!ptn.contains(obj)) {
                ptn.addObject(obj);
                difference.addObject(obj);
            }
        }
        if (!difference.isEmpty()) {
            for (Pointer s : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(s, pointsToSet);
            }
        }
        return difference;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (Invoke invoke: var.getInvokes()) {
            var method = resolveCallee(recv, invoke);
            var _this = method.getIR().getThis();
            workList.addEntry(pointerFlowGraph.getVarPtr(_this), new PointsToSet(recv));
            Edge<Invoke, JMethod> edge = null;
            if (invoke.isVirtual()) {
                edge = new Edge<Invoke, JMethod>(CallKind.VIRTUAL, invoke, method);
            } else if (invoke.isInterface()) {
                edge = new Edge<Invoke, JMethod>(CallKind.INTERFACE, invoke, method);
            } else if (invoke.isSpecial()) {
                edge = new  Edge<Invoke, JMethod>(CallKind.SPECIAL, invoke, method);
            }
            else {
                throw new RuntimeException("Unsupported invoke " + invoke);
            }

            if (edge != null && callGraph.addEdge(edge)) {
                doProcessCall(invoke, method);
            }

        }
    }

    private void doProcessCall(Invoke invoke, JMethod method) {
        addReachable(method);
        var params = method.getIR().getParams();
        var args = invoke.getInvokeExp().getArgs();
        assert params.size() == args.size();
        for (int i = 0; i < params.size(); i++) {
            var paramPtr = pointerFlowGraph.getVarPtr(params.get(i));
            var argPtr = pointerFlowGraph.getVarPtr(args.get(i));
            addPFGEdge(argPtr, paramPtr);
        }

        var retVal = invoke.getResult();
        if (retVal != null) {
            var methodRet = method.getIR().getReturnVars();
            for (var methodRetVar: methodRet) {
                var methodRetPtr = pointerFlowGraph.getVarPtr(methodRetVar);
                var returnValPtr = pointerFlowGraph.getVarPtr(retVal);
                addPFGEdge(methodRetPtr, returnValPtr);
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
