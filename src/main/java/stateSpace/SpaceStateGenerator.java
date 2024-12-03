package stateSpace;

import com.rits.cloning.Cloner;
import dataStructure.*;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.*;
import org.rebecalang.compiler.modelcompiler.hybridrebeca.objectmodel.HybridRebecaCode;
import org.rebecalang.compiler.modelcompiler.hybridrebeca.objectmodel.PhysicalClassDeclaration;
import sos.NonTimeProgressSOSExecutor;
import utils.CompilerUtil;
import utils.ReachabilityAnalysisGraph;
import visitors.BlockStatementExecutorVisitor;
import visitors.ExpressionEvaluatorVisitor;

import java.math.BigDecimal;
import java.util.*;

import static stateSpace.HybridState.extractVariableNames;

public class SpaceStateGenerator {

    public SpaceStateGenerator() {

    }

    @FunctionalInterface
    public interface JoszefCaller {
        double[] call(String[] ODEs, double[] intervals, double[] reachParams);
    }

    public void analyzeReachability(JoszefCaller joszefCaller) {
         // must be tupple
        double endSimulation = 3;

        NonTimeProgressSOSExecutor nonTimeProgressSOSExecutor = new NonTimeProgressSOSExecutor();
        final HybridRebecaCode hybridRebecaCode = CompilerUtil.getHybridRebecaCode();
        HybridState initialState = makeInitialState();
        ReachabilityAnalysisGraph reachabilityAnalysisGraph = new ReachabilityAnalysisGraph(initialState);
        Queue<HybridState> queue = new LinkedList<>(nonTimeProgressSOSExecutor.generateNextStates(initialState, false));
        Boolean isFirstRound = true;
        while (!queue.isEmpty() && isReachedEndYet(queue, endSimulation)) { // should add time upper bound
            double currentEvent = 0.0;
            HybridState state = queue.poll();
            currentEvent = state.getGlobalTime().getLowerBound();
            state.updateHash();

            ReachabilityAnalysisGraph.TreeNode rootNode = reachabilityAnalysisGraph.findNodeInGraph(state);

            List<Set<String>> globalStateModes = state.getGlobalStateModes();

            String[] ODEs = RebecInstantiationMapping.getInstance().getCurrentFlows(globalStateModes);

            double[] intervals = state.getIntervals(ODEs);
            double timeStep = 1;
            double[] nextEvents = state.getEvents(currentEvent, timeStep);
            double previousEvent = currentEvent;
            currentEvent = Arrays.stream(nextEvents).min().orElseThrow();

            double[] reachParams = new double[]{10.0, 0.99, 0.01, 7.0, currentEvent - previousEvent};

            Cloner cloner = new Cloner();
            HybridState updatedPhysicalHybridState = cloner.deepClone(state);
            if (isFirstRound) {
                updatedPhysicalHybridState.updateGlobalTime(0, currentEvent);
            }
            else {
                updatedPhysicalHybridState.updateGlobalTime(currentEvent, currentEvent - state.getGlobalTime().getLowerBound() + state.getGlobalTime().getUpperBound());
            }
            Map<String, HybridState> updatedPhysicalHybridStates = new HashMap<>();
            updatedPhysicalHybridStates.put(updatedPhysicalHybridState.updateHash(), updatedPhysicalHybridState);
            if (ODEs.length > 0) {
                double[] result = joszefCaller.call(ODEs, intervals, reachParams);
                //                double[] result = {0.0, 0.0, 20.0, 20.0, 0.0, 0.01, 20.0, 20.0};
                int index = 0;
                int StartIndex = result.length - 2 * ODEs.length;
                for (String ODE : ODEs) {
                    String[] components = extractVariableNames(ODE);
                    String physicalClassName = components[0], odeVariableName = components[1];
                    double odeVariableLowerBound, odeVariableUpperBound;
                    if (isFirstRound) {
                        odeVariableLowerBound = result[2 * index];
                        odeVariableUpperBound = result[(index * 2) + 1 + StartIndex];
                        if (odeVariableUpperBound < odeVariableLowerBound) {
                            double swap;
                            swap = odeVariableUpperBound;
                            odeVariableUpperBound = odeVariableLowerBound;
                            odeVariableLowerBound = swap;
                        }
                    }
                    else {
                        odeVariableLowerBound = result[2 * index + StartIndex];
                        odeVariableUpperBound = result[(index * 2) + 1 + StartIndex];
                    }
                    PhysicalState physicalState = (PhysicalState) updatedPhysicalHybridState.getActorState(physicalClassName);
                    physicalState.updateVariable(new IntervalRealVariable(odeVariableName, odeVariableLowerBound, odeVariableUpperBound));
                    index++;
                }
                isFirstRound = false;
            }

            try {
                updatePhysicalStates(updatedPhysicalHybridState.getPhysicalStates(), updatedPhysicalHybridStates);
            } catch (Exception ex){
                System.out.println("Deadlock happened");
                reachabilityAnalysisGraph.addNode(rootNode, updatedPhysicalHybridState, "PhysicalUpdate");
                continue;
            }
            for (Map.Entry<String, HybridState> hybridStateEntry : updatedPhysicalHybridStates.entrySet()) {
                hybridStateEntry.getValue().updateHash();
                reachabilityAnalysisGraph.addNode(rootNode, hybridStateEntry.getValue(), "PhysicalUpdate");
                List<HybridState> generatedHybridStates = nonTimeProgressSOSExecutor.generateNextStates(hybridStateEntry.getValue(), false);
                queue.addAll(generatedHybridStates);
                ReachabilityAnalysisGraph.TreeNode rootTempNode = reachabilityAnalysisGraph.findNodeInGraph(hybridStateEntry.getValue());
                for (HybridState hybridState : generatedHybridStates) {
                    if (!hybridStateEntry.getValue().getHash().equals(hybridState.getHash()))
                        reachabilityAnalysisGraph.addNode(rootTempNode, hybridState, " NonTimeProgressExecute");
                }
            }
        }
        String graph = reachabilityAnalysisGraph.toDot();
    }

    private Boolean isReachedEndYet(Queue<HybridState> queue, double endSimulation) {
        for (HybridState hybridState : queue) {
            if (hybridState.getGlobalTime().getLowerBound() < endSimulation) // CHECKME: Don't need to remove states which endSimulation < UpperBound as it is BFS
                return true;
        }
        return false;
    }

    private static void updatePhysicalStates(HashMap<String, PhysicalState> physicalStates, Map<String, HybridState> updatedPhysicalHybridStates) {
        for (Map.Entry<String, PhysicalState>  physicalStateEntry :  physicalStates.entrySet()) {
            Map<String, HybridState> shallowCopyCurrentStates = new HashMap<>(updatedPhysicalHybridStates);
            for (Map.Entry<String, HybridState> hybridStateEntry : shallowCopyCurrentStates.entrySet()) {

                PhysicalState physicalState = hybridStateEntry.getValue().getPhysicalStates().get(physicalStateEntry.getKey());

                ExpressionEvaluatorVisitor evaluatorVisitor = new ExpressionEvaluatorVisitor(physicalState.getVariablesValuation());
                String physicalDeclarationName = RebecInstantiationMapping.getInstance().getRebecReactiveClassType(physicalState.getActorName());
                DiscreteBoolVariable guardSatisfiedResult = (DiscreteBoolVariable) evaluatorVisitor.visit(
                        (BinaryExpression) Objects.requireNonNull(CompilerUtil.getGuardCondition(physicalDeclarationName, physicalState.getMode())));
                DiscreteBoolVariable invariantSatisfiedResult = (DiscreteBoolVariable) evaluatorVisitor.visit(
                        (BinaryExpression) Objects.requireNonNull(CompilerUtil.getInvariantCondition(physicalDeclarationName, physicalState.getMode())));
                PhysicalClassDeclaration physicalClassDeclaration = CompilerUtil.getPhysicalClassDeclaration(physicalDeclarationName);

                if (invariantSatisfiedResult.getDefinite()) {
                    if (invariantSatisfiedResult.getValue()) {
                        // CHECKME
                        checkGuardIfInvariantIsTrue(updatedPhysicalHybridStates, physicalStateEntry, hybridStateEntry,
                                guardSatisfiedResult, physicalDeclarationName);
                    } else {
                        System.out.println("Deadlock happened:");
                        System.out.println(hybridStateEntry.getValue());
                        if (updatedPhysicalHybridStates.size() <= 1) {
                            throw new RuntimeException("Deadlock happened");
                        } else {
                            updatedPhysicalHybridStates.remove(hybridStateEntry.getKey());
                        }
                    }
                } else {
                    checkGuardIfInvariantIsTrue(updatedPhysicalHybridStates, physicalStateEntry, hybridStateEntry,
                            guardSatisfiedResult, physicalDeclarationName);
                }
//            }
            }
        }
    }

    private static void checkGuardIfInvariantIsFalse(DiscreteBoolVariable guardSatisfiedResult,
                                                     String physicalDeclarationName, PhysicalState physicalState) {
        if (guardSatisfiedResult.getDefinite()) {
            if (guardSatisfiedResult.getValue()) {
                List<Statement> guardStatements =
                        Objects.requireNonNull(CompilerUtil.getModeDeclaration(physicalDeclarationName
                                , physicalState.getMode())).getGuardDeclaration().getBlock().getStatements();
                physicalState.addStatements(guardStatements);
            } else {
                throw new RuntimeException("Time lock happened");
            }
        } else {
            List<Statement> guardStatements =
                    Objects.requireNonNull(CompilerUtil.getModeDeclaration(physicalDeclarationName,
                            physicalState.getMode())).getGuardDeclaration().getBlock().getStatements();
            physicalState.addStatements(guardStatements);
        }
    }

    private static void checkGuardIfInvariantIsTrue(Map<String, HybridState> updatedPhysicalHybridStates,
                                                    Map.Entry<String, PhysicalState> physicalStateEntry,
                                                    Map.Entry<String, HybridState> hybridStateEntry,
                                                    DiscreteBoolVariable guardSatisfiedResult,
                                                    String physicalDeclarationName) {
        if ((guardSatisfiedResult.getDefinite() && guardSatisfiedResult.getValue()) || !guardSatisfiedResult.getDefinite()) {
            Cloner cloner = new Cloner();
            HybridState newHybridState = cloner.deepClone(hybridStateEntry.getValue());
            PhysicalState newPhysicalState = newHybridState.getPhysicalStates().get(physicalStateEntry.getKey());
            List<Statement> guardStatements =
                    Objects.requireNonNull(CompilerUtil.getModeDeclaration(physicalDeclarationName,
                            newPhysicalState.getMode())).getGuardDeclaration().getBlock().getStatements();
            newPhysicalState.addStatements(guardStatements);
            updatedPhysicalHybridStates.put(newHybridState.updateHash(), newHybridState);
        }
    }

    private HybridState makeInitialState() {
        final HybridRebecaCode hybridRebecaCode = CompilerUtil.getHybridRebecaCode();
        HashMap<String, SoftwareState> softwareStates = new HashMap<>();
        HashMap<String, PhysicalState> physicalStates = new HashMap<>();

        List<MainRebecDefinition> mainRebecDefinitions = CompilerUtil.getHybridRebecaCode().getMainDeclaration().getMainRebecDefinition();
        for (MainRebecDefinition mainRebecDefinition : mainRebecDefinitions) {
            OrdinaryPrimitiveType type = (OrdinaryPrimitiveType) mainRebecDefinition.getType();
            ReactiveClassDeclaration reactiveClassDeclaration = CompilerUtil.getReactiveClassDeclaration(type.getName());
            if (reactiveClassDeclaration == null) {
                PhysicalClassDeclaration physicalClassDeclaration = CompilerUtil.getPhysicalClassDeclaration(type.getName());
                if (physicalClassDeclaration == null) {
                    throw new RuntimeException("Main class not found");
                }
//                physicalStates.add(createPhysicalState(physicalClassDeclaration, mainRebecDefinition));
                PhysicalState physicalState = createPhysicalState(physicalClassDeclaration, mainRebecDefinition);
                physicalStates.put(physicalState.getActorName(), physicalState);
            } else {
//                softwareStates.add(createSoftwareState(reactiveClassDeclaration, mainRebecDefinition));
                SoftwareState softwareState = createSoftwareState(reactiveClassDeclaration, mainRebecDefinition);
                softwareStates.put(softwareState.getActorName(), softwareState);
            }
        }
        return new HybridState(new ContinuousVariable("globalTime"), softwareStates, physicalStates, new CANNetworkState());
    }

    private SoftwareState createSoftwareState(ReactiveClassDeclaration reactiveClassDeclaration, MainRebecDefinition mainRebecDefinition) {
        ConstructorDeclaration constructorDeclaration = getConstructor(reactiveClassDeclaration.getConstructors(), mainRebecDefinition.getArguments());
        if (constructorDeclaration == null) {
            throw new RuntimeException("Constructor not found");
        }
        Map<String, Variable> variableValuationInitial = new HashMap<>();
        ExpressionEvaluatorVisitor expressionEvaluatorVisitor = new ExpressionEvaluatorVisitor(new HashMap<>());
        for (FormalParameterDeclaration formalParameterDeclaration : constructorDeclaration.getFormalParameters()) {
            Variable variable = expressionEvaluatorVisitor.visit(mainRebecDefinition.getArguments().get(constructorDeclaration.getFormalParameters().indexOf(formalParameterDeclaration)));
            variableValuationInitial.put(formalParameterDeclaration.getName(), variable);
        }

        List<FieldDeclaration> stateVars = reactiveClassDeclaration.getStatevars();
        for (FieldDeclaration stateVar : stateVars) {
            String type = ((OrdinaryPrimitiveType) stateVar.getType()).getName();
            for (VariableDeclarator variableDeclarator : stateVar.getVariableDeclarators()) {
                switch (type) {
                    case "int":
                    case "byte":
                    case "short": {
                        variableValuationInitial.put(variableDeclarator.getVariableName(),
                                new DiscreteDecimalVariable(variableDeclarator.getVariableName(), new BigDecimal(0)));
                        break;
                    }
                    case "float":
                    case "double": {
                        variableValuationInitial.put(variableDeclarator.getVariableName(),
                                new IntervalRealVariable(variableDeclarator.getVariableName(), 0.0));
                        break;
                    }
                    case "boolean": {
                        variableValuationInitial.put(variableDeclarator.getVariableName(),
                                new DiscreteBoolVariable(variableDeclarator.getVariableName(), false));
                        break;
                    }
                }
            }

        }
        BlockStatementExecutorVisitor blockStatementExecutorVisitor = new BlockStatementExecutorVisitor(variableValuationInitial);
        blockStatementExecutorVisitor.visit(constructorDeclaration.getBlock());
        HashMap<String, Variable> variableValuation = new HashMap<>();
        for (FieldDeclaration stateVar : stateVars) {
            for (VariableDeclarator variableDeclarator : stateVar.getVariableDeclarators()) {
                variableValuation.put(variableDeclarator.getVariableName(), variableValuationInitial.get(variableDeclarator.getVariableName()));
            }
        }
        return new SoftwareState(mainRebecDefinition.getName(), variableValuation, new HashSet<>(), new ArrayList<>(), 0, new ContinuousVariable("resumeTime"));


    }

    private PhysicalState createPhysicalState(PhysicalClassDeclaration physicalClassDeclaration, MainRebecDefinition mainRebecDefinition) {
        ConstructorDeclaration constructorDeclaration = getConstructor(physicalClassDeclaration.getConstructors(), mainRebecDefinition.getArguments());
        if (constructorDeclaration == null) {
            throw new RuntimeException("Constructor not found");
        }
        Map<String, Variable> variableValuationInitial = new HashMap<>();
        ExpressionEvaluatorVisitor expressionEvaluatorVisitor = new ExpressionEvaluatorVisitor(new HashMap<>());
        for (FormalParameterDeclaration formalParameterDeclaration : constructorDeclaration.getFormalParameters()) {
            Variable variable = expressionEvaluatorVisitor.visit(mainRebecDefinition.getArguments().get(constructorDeclaration.getFormalParameters().indexOf(formalParameterDeclaration)));
            variableValuationInitial.put(formalParameterDeclaration.getName(), variable);
        }

        List<FieldDeclaration> stateVars = physicalClassDeclaration.getStatevars();
        for (FieldDeclaration stateVar : stateVars) {
            String type = ((OrdinaryPrimitiveType) stateVar.getType()).getName();
            for (VariableDeclarator variableDeclarator : stateVar.getVariableDeclarators()) {
                switch (type) {
                    case "int":
                    case "byte":
                    case "short": {
                        variableValuationInitial.put(variableDeclarator.getVariableName(),
                                new DiscreteDecimalVariable(variableDeclarator.getVariableName(), new BigDecimal(0)));
                        break;
                    }
                    case "float":
                    case "double": {
                        variableValuationInitial.put(variableDeclarator.getVariableName(),
                                new IntervalRealVariable(variableDeclarator.getVariableName(), 0.0));
                        break;
                    }
                    case "boolean": {
                        variableValuationInitial.put(variableDeclarator.getVariableName(),
                                new DiscreteBoolVariable(variableDeclarator.getVariableName(), false));
                        break;
                    }
                }
            }

        }
        BlockStatementExecutorVisitor blockStatementExecutorVisitor = new BlockStatementExecutorVisitor(variableValuationInitial, "none");
        blockStatementExecutorVisitor.visit(constructorDeclaration.getBlock());
        HashMap<String, Variable> variableValuation = new HashMap<>();
        for (FieldDeclaration stateVar : stateVars) {
            for (VariableDeclarator variableDeclarator : stateVar.getVariableDeclarators()) {
                variableValuation.put(variableDeclarator.getVariableName(), variableValuationInitial.get(variableDeclarator.getVariableName()));
            }
        }
        return new PhysicalState(mainRebecDefinition.getName(), blockStatementExecutorVisitor.getMode(), variableValuation, new HashSet<>(), new ArrayList<>(), 0);
    }

    private ConstructorDeclaration getConstructor(List<ConstructorDeclaration> constructorDeclarations, List<Expression> declarationArgs) {
        for (ConstructorDeclaration constructorDeclaration : constructorDeclarations) {
            List<FormalParameterDeclaration> parameterDeclarations = constructorDeclaration.getFormalParameters();
            if (parameterDeclarations.size() != declarationArgs.size()) {
                continue;
            }
            boolean isFound = true;
            for (FormalParameterDeclaration parameterDeclaration : parameterDeclarations) {
                OrdinaryPrimitiveType formalParameterType = (OrdinaryPrimitiveType) parameterDeclaration.getType();
                OrdinaryPrimitiveType actualParameterType = ((OrdinaryPrimitiveType) declarationArgs.get(parameterDeclarations.indexOf(parameterDeclaration)).getType());
                if (!formalParameterType.getName().equals(actualParameterType.getName())) {
                    isFound = false;
                    break;
                }
            }
            if (isFound) {
                return constructorDeclaration;
            }
        }
        return null;
    }
}
