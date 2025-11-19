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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);

        ArrayList<JMethod> worklist = new ArrayList<>();
        worklist.add(entry);
        while (!worklist.isEmpty()) {
            JMethod current = worklist.remove(0);
            if (!callGraph.contains(current)) {
                callGraph.addReachableMethod(current);
                callGraph.callSitesIn(current).forEach(cs -> {
                    resolve(cs).forEach(method -> {
                        if (method != null){
                            worklist.add(method);
                            callGraph.addEdge(new Edge<Invoke, JMethod>(CallGraphs.getCallKind(cs), cs, method));
                        }
                    });
                });
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        HashSet<JMethod> candidates = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        var declaredClass = methodRef.getDeclaringClass();
        var sig = methodRef.getSubsignature();

        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC ->
                candidates.add(declaredClass.getDeclaredMethod(sig));
            case SPECIAL ->
                candidates.add(dispatch(declaredClass, sig));
            case VIRTUAL, INTERFACE -> {
                ArrayList<JClass> worklist = new ArrayList<>();
                HashSet<JClass> visited = new HashSet<>();
                worklist.add(declaredClass);
                while (!worklist.isEmpty()) {
                    JClass jclass = worklist.remove(0);
                    if (visited.add(jclass)) {
                        if (jclass.isInterface()) {
                            worklist.addAll(hierarchy.getDirectImplementorsOf(jclass));
                            worklist.addAll(hierarchy.getDirectSubinterfacesOf(jclass));
                        }
                        worklist.addAll(hierarchy.getDirectSubclassesOf(jclass));
                    }
                    candidates.add(dispatch(jclass, sig));
                }
            }
        }
        return candidates;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        var fn = jclass.getDeclaredMethod(subsignature);
        if (fn == null || fn.isAbstract()) {
            var superClass = jclass.getSuperClass();
            if (superClass != null) {
                fn = dispatch(superClass, subsignature);
            }
        }
        return fn;
    }
}
