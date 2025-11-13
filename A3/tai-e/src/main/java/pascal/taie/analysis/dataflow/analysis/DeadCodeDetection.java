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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        deadCode.addAll(ir.getStmts());

        ArrayList<Stmt> worklist = new ArrayList<>();
        HashSet<Stmt> visited = new HashSet<>();
        worklist.add(cfg.getEntry());
        visited.add(cfg.getEntry());
        while (!worklist.isEmpty()) {
            var stmt = worklist.remove(0);
            // control flow unreachable
            deadCode.remove(stmt);

            // if branch unreachable
            if (stmt instanceof If ifStmt) {
                var cond = ifStmt.getCondition();
                var factSet = constants.getInFact(ifStmt);

                var condRes = ConstantPropagation.evaluate(cond, factSet);
                if (condRes.isConstant()) {
                    var reachablePath = condRes.getConstant() == 0 ? Edge.Kind.IF_FALSE : Edge.Kind.IF_TRUE;
                    cfg.getOutEdgesOf(stmt).stream().filter(stmtEdge -> stmtEdge.getKind() == reachablePath).findFirst().ifPresent( reachableNode -> {
                        if (!visited.contains(reachableNode.getTarget())) {
                            worklist.add(reachableNode.getTarget());
                            visited.add(reachableNode.getTarget());
                        }
                    });
                }
                else {
                    cfg.getSuccsOf(stmt).forEach(st -> {
                        if (!visited.contains(st)) {
                            worklist.add(st);
                            visited.add(st);
                        }
                    });
                }
            }
            // switch branch unreachable
            else if (stmt instanceof SwitchStmt switchStmt) {
                var condVar = switchStmt.getVar();
                var factSet = constants.getInFact(switchStmt);
                if (factSet.get(condVar).isConstant()) {
                    var constVal = factSet.get(condVar).getConstant();
                    var targetStmt = switchStmt.getCaseTargets().stream().filter(pair -> pair.first().equals(constVal)).findFirst().map(Pair::second).orElse(switchStmt.getDefaultTarget());

                    if (!visited.contains(targetStmt)){
                        worklist.add(targetStmt);
                        visited.add(targetStmt);
                    }
                }
                else {
                    cfg.getSuccsOf(stmt).forEach(st -> {
                        if (!visited.contains(st)) {
                            worklist.add(st);
                            visited.add(st);
                        }
                    });
                }
            }
            // unused assignment
            else if (stmt instanceof AssignStmt assignStmt) {
                var def = assignStmt.getDef();
                List<RValue> uses = (List<RValue>) assignStmt.getUses();
                var outFact = liveVars.getOutFact(assignStmt);

                // dead assignment if out not contains def
                def.ifPresent(defVal -> {
                    if (defVal instanceof Var defVar && uses.stream().allMatch(DeadCodeDetection::hasNoSideEffect)) {
                        if (!outFact.contains(defVar)) {
                            deadCode.add(assignStmt);
                        }
                    }
                });

                cfg.getSuccsOf(stmt).forEach(st -> {
                    if (!visited.contains(st)) {
                        worklist.add(st);
                        visited.add(st);
                    }
                });
            }
            else {

                cfg.getSuccsOf(stmt).forEach(st -> {
                    if (!visited.contains(st)) {
                        worklist.add(st);
                        visited.add(st);
                    }
                });
            }
        }

        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
