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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        var fact = new CPFact();
        for (var param: cfg.getIR().getParams()) {
            if (canHoldInt(param))
                fact.update(param, Value.getNAC());
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.keySet().forEach(var -> {
            if (canHoldInt(var))
                target.update(var, this.meetValue(fact.get(var), target.get(var)));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isUndef() && v2.isUndef()) {
            return v1;
        }
        if (v1.isUndef()) {
            return v2;
        }
        if (v2.isUndef()) {
            return v1;
        }

        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }

        if (v1.isConstant() && v2.isConstant()) {
            if (v1.getConstant() == v2.getConstant()) {
                return v1;
            }
            return Value.getNAC();
        }
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt.getDef().isEmpty()) {
            return out.copyFrom(in);
        }

        if (stmt instanceof DefinitionStmt defStmt) {
            if (defStmt.getDef().isPresent() &&
                    defStmt.getLValue() instanceof Var lVar) {
                if (canHoldInt(lVar)) {
                    RValue rValue = defStmt.getRValue();
                    CPFact newOut = in.copy();
                    if (rValue instanceof IntLiteral literal) {
                        newOut.update(lVar, Value.makeConstant(literal.getValue()));
                    } else if (rValue instanceof Var rVar) {
                        if (canHoldInt(rVar)) {
                            newOut.update(lVar, in.get(rVar));
                        }
                    } else if (rValue instanceof BinaryExp binExpr) {
                        var res = evaluate(binExpr, in);

                        if (res != null) {
                            newOut.update(lVar, res);
                        }
                    } else {
                        newOut.update(lVar, Value.getNAC());
                    }
                    return out.copyFrom(newOut);
                }
            }
        }
        return out.copyFrom(in);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(BinaryExp exp, CPFact in) {
        // TODO - finish me

        if (!canHoldInt(exp.getOperand1()) || !canHoldInt(exp.getOperand2()))
            return Value.getUndef();

        var lVal = in.get(exp.getOperand1());
        var rVal = in.get(exp.getOperand2());

        if (lVal.isConstant() && rVal.isConstant()) {
            if (exp instanceof BitwiseExp bitwiseExp) {
                return switch (bitwiseExp.getOperator()) {
                    case AND -> Value.makeConstant(lVal.getConstant() & rVal.getConstant());
                    case OR -> Value.makeConstant(lVal.getConstant() | rVal.getConstant());
                    case XOR -> Value.makeConstant(lVal.getConstant() ^ rVal.getConstant());
                };
            }
            if (exp instanceof ArithmeticExp arithExp) {
                return switch (arithExp.getOperator()) {
                    case ADD -> Value.makeConstant(lVal.getConstant() + rVal.getConstant());
                    case SUB -> Value.makeConstant(lVal.getConstant() - rVal.getConstant());
                    case MUL -> Value.makeConstant(lVal.getConstant() * rVal.getConstant());
                    case DIV -> rVal.getConstant() == 0 ? Value.getUndef() : Value.makeConstant(lVal.getConstant() / rVal.getConstant());
                    case REM -> rVal.getConstant() == 0 ? Value.getUndef() : Value.makeConstant(lVal.getConstant() % rVal.getConstant());
                };
            }
            if (exp instanceof ConditionExp conditionExp) {
                return switch (conditionExp.getOperator()) {
                  case EQ -> Value.makeConstant(lVal.getConstant() == rVal.getConstant() ? 1 : 0);
                  case NE ->  Value.makeConstant(lVal.getConstant() != rVal.getConstant() ? 1 : 0);
                  case LT -> Value.makeConstant(lVal.getConstant() < rVal.getConstant() ? 1 : 0);
                  case GT -> Value.makeConstant(lVal.getConstant() > rVal.getConstant() ? 1 : 0);
                  case LE -> Value.makeConstant(lVal.getConstant() <= rVal.getConstant() ? 1 : 0);
                  case GE -> Value.makeConstant(lVal.getConstant() >= rVal.getConstant() ? 1 : 0);
                };
            }
            if (exp instanceof ShiftExp shiftExp) {
                return switch (shiftExp.getOperator()) {
                    case SHL -> Value.makeConstant(lVal.getConstant() << rVal.getConstant());
                    case SHR -> Value.makeConstant(lVal.getConstant() >> rVal.getConstant());
                    case USHR -> Value.makeConstant(lVal.getConstant() >>> rVal.getConstant());
                };
            }
            throw new UnsupportedOperationException();
        }

        if (rVal.isConstant() && rVal.getConstant() == 0) {
            if (exp instanceof ArithmeticExp arithExp) {
                switch (arithExp.getOperator()) {
                    case DIV :
                    case REM :
                            return Value.getUndef();
                }
            }
        }
        if (lVal.isNAC() || rVal.isNAC()) {
            return Value.getNAC();
        }
        return Value.getUndef();
    }
}
