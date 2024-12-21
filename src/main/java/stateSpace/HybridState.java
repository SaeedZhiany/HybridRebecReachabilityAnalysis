package stateSpace;

import com.rits.cloning.Cloner;
import dataStructure.*;
import org.rebecalang.compiler.modelcompiler.corerebeca.objectmodel.*;
import org.rebecalang.compiler.modelcompiler.timedrebeca.objectmodel.TimedRebecaParentSuffixPrimary;
import utils.CompilerUtil;
import utils.StringSHA256;
import visitors.ExpressionEvaluatorVisitor;

import javax.annotation.Nonnull;
import java.math.BigDecimal;
import java.util.*;

public class HybridState {
    // CHECKME: should global time be non-null?
//    @Nonnull
    private ContinuousVariable globalTime;
    //    @Nonnull
    private HashMap<String, SoftwareState> softwareStates;
    //    @Nonnull
    private HashMap<String, PhysicalState> physicalStates;
    //    @Nonnull
    private CANNetworkState CANNetworkState;
    //    @Nonnull
    private String hashString;
    private String parentHash;


    public HybridState() {
        // FIXME: is this the correct way to initialize globalTime?
        // ContinuousVariable globalTime = new ContinuousVariable("globalTime");
        this(new ContinuousVariable("globalTime"), new HashMap<>(), new HashMap<>(), new CANNetworkState());
    }

    public HybridState(HybridState hybridState) {
        // CHECKME: aren't this attributes private?
        this.globalTime = new ContinuousVariable(hybridState.globalTime);
        HashMap<String, SoftwareState> newSoftwareStates = new HashMap<>();
        for (SoftwareState softwareState : hybridState.softwareStates.values()) {
            newSoftwareStates.put(softwareState.actorName, new SoftwareState(softwareState));
        }
        this.softwareStates = newSoftwareStates;
        HashMap<String, PhysicalState> newPhysicalStates = new HashMap<>();
        for (PhysicalState physicalState : hybridState.physicalStates.values()) {
            newPhysicalStates.put(physicalState.actorName, new PhysicalState(physicalState));
        }
        this.physicalStates = newPhysicalStates;
//        this.CANNetworkState = new CANNetworkState(hybridState.CANNetworkState);
    }

    public HybridState(
            @Nonnull ContinuousVariable globalTime,
            @Nonnull HashMap<String, SoftwareState> softwareStates,
            @Nonnull HashMap<String, PhysicalState> physicalStates,
            @Nonnull stateSpace.CANNetworkState CANNetworkState
    ) {
        this.globalTime = globalTime;
        this.softwareStates = softwareStates;
        this.physicalStates = physicalStates;
//        this.CANNetworkState = CANNetworkState;
        // CHECKME: is this the correct way to handle hashString exception?
        try {
            this.hashString = updateHash();
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    public boolean equals(HybridState state) {
        String thisHashString = this.getHash();
        String stateHashString = state.getHash();
        if (thisHashString != stateHashString) {
            return false;
        }
        // TODO: make sure that the 2 states are actually equal
        return true;
    }

    private void replaceSoftwareState(SoftwareState softwareState) {
        softwareStates.replace(softwareState.actorName, softwareState);
    }

    private void replacePhysicalState(PhysicalState physicalState) {
        physicalStates.replace(physicalState.actorName, physicalState);
    }

    public void replaceActorState(ActorState actorState) {
        if (actorState instanceof SoftwareState) {
            replaceSoftwareState((SoftwareState) actorState);
        } else if (actorState instanceof PhysicalState) {
            replacePhysicalState((PhysicalState) actorState);
        }
        // CHECKME: else
        try {
            this.updateHash();
        } catch (Exception e) {
            // FIXME: is this the correct way to handle this exception?
            throw new RuntimeException(e);
        }
    }

    @Override
    public String toString() {
        // CHECKME: the order of the states is not guaranteed, is it a problem?
        StringBuilder stringBuilder = new StringBuilder();

        stringBuilder.append(globalTime).append("\n");

        for (SoftwareState softwareState : softwareStates.values()) {
            stringBuilder.append(softwareState.toString());
            stringBuilder.append(";");
        }
        stringBuilder.append("\n");
        for (PhysicalState physicalState : physicalStates.values()) {
            stringBuilder.append(physicalState.toString());
            stringBuilder.append(";");
        }
        // stringBuilder.append(CANNetworkState.toString());
        return stringBuilder.toString();
    }

    // CHECKME: when should we call this method?
    public String updateHash() {
        this.hashString = StringSHA256.hashString(this.toString());
        return this.hashString;
    }

    public String getHash() {
        return this.updateHash();
    }

    public HashMap<String, PhysicalState> getPhysicalStates() {
        return this.physicalStates;
    }

    public HashMap<String, SoftwareState> getSoftwareStates() {
        return this.softwareStates;
    }

    private void resetResumeTime(ActorState actorState) {
        if (actorState instanceof SoftwareState) {
            ((SoftwareState) actorState).setResumeTime(new ContinuousVariable("resume time"));
        }
    }

    private HybridState createSuspendedState(ActorState actorState) {
        if (actorState instanceof SoftwareState) {
            Cloner cloner = new Cloner();
            ActorState newActorState = cloner.deepClone(actorState);
            HybridState newHybridState = cloner.deepClone(this);
            if (isNonDeterministicInResumeTime(((SoftwareState) newActorState).getResumeTime())) {
                ContinuousVariable resumeTime = ((SoftwareState) newActorState).getResumeTime();
                ((SoftwareState) newActorState).setResumeTime(new ContinuousVariable("resume time", globalTime.getUpperBound(), resumeTime.getUpperBound()));
                newHybridState.replaceActorState(newActorState);
                return newHybridState;
            }
        }
        return null;
    }

    public boolean isSuspended(ContinuousVariable resumeTime) {
        if ((resumeTime.getLowerBound().compareTo(this.globalTime.getLowerBound()) <= 0)) { // the less than never happens, just for the sake of completeness
            return false;
        }
        return true;
    }

    private boolean isNonDeterministicInResumeTime(ContinuousVariable resumeTime) {
        if ((resumeTime.getLowerBound().compareTo(this.globalTime.getLowerBound()) <= 0) &&
                (resumeTime.getUpperBound().compareTo(this.globalTime.getUpperBound())) > 0) {
            return true;
        }
        return false;
    }

    public List<HybridState> takeMessage(ActorState actorState) {
        // TODO: call takeMessage method on actorState and retrieve the new actorStates
        // TODO: takeMessage method of SoftwareState can and should return multiple (at most 2?!) newSoftwareStates
        // CHECKME: does it call on correct class? (software and physical)
        List<HybridState> result = new ArrayList<>();
        List<ActorState> generatedActorStates = actorState.takeMessage(globalTime);
        for (ActorState actorStateItr : generatedActorStates) {
            Cloner cloner = new Cloner();
            HybridState newHybridState = cloner.deepClone(this);
            ActorState newActorState = cloner.deepClone(actorStateItr);
            resetResumeTime(newActorState);
            newHybridState.replaceActorState(newActorState);
            result.add(newHybridState);
        }
        HybridState suspendedState = createSuspendedState(actorState);
        if (suspendedState != null) {
            result.add(suspendedState);
        }
        return result;
    }

    private ContinuousVariable getDelayAfterTime(Expression lowerBoundExp, Expression upperBoundExp, Expression exp, ExpressionEvaluatorVisitor evaluatorVisitor) {
        Variable lowerBound = (lowerBoundExp != null) ? evaluatorVisitor.visit(lowerBoundExp) : null;
        Variable upperBound = (upperBoundExp != null) ? evaluatorVisitor.visit(upperBoundExp) : null;
        Variable after = (exp != null) ? evaluatorVisitor.visit(exp) : null;

        ContinuousVariable messageArrivalTime = new ContinuousVariable(globalTime);
        if (after != null) {
            if (after instanceof IntervalRealVariable) {
                messageArrivalTime.setLowerBound(globalTime.getLowerBound() + ((IntervalRealVariable) after).getLowerBound());
                messageArrivalTime.setUpperBound(globalTime.getUpperBound() + ((IntervalRealVariable) after).getUpperBound());
            } else {
                messageArrivalTime.setLowerBound(globalTime.getLowerBound() + ((DiscreteDecimalVariable) after).getValue().doubleValue());
                messageArrivalTime.setUpperBound(globalTime.getUpperBound() + (((DiscreteDecimalVariable) after).getValue().doubleValue()));
            }
        }

        if (lowerBound != null) {
            if (lowerBound instanceof IntervalRealVariable) {
                messageArrivalTime.setLowerBound(globalTime.getLowerBound() + (((IntervalRealVariable) lowerBound).getLowerBound()));
            } else {
                messageArrivalTime.setLowerBound(globalTime.getLowerBound() + (((DiscreteDecimalVariable) lowerBound).getValue().doubleValue()));
            }
        }

        if (upperBound != null) {
            if (upperBound instanceof IntervalRealVariable) {
                messageArrivalTime.setUpperBound(globalTime.getUpperBound() + (((IntervalRealVariable) upperBound).getUpperBound()));
            } else {
                messageArrivalTime.setUpperBound(globalTime.getUpperBound() + (((DiscreteDecimalVariable) upperBound).getValue().doubleValue()));
            }
        }

        return messageArrivalTime;
    }

    private HashMap<String, Variable> getMessageCallParameter(String receiver, String serverName, ExpressionEvaluatorVisitor evaluatorVisitor, DotPrimary sendStatement) {
        List<FormalParameterDeclaration> serverParams = CompilerUtil.getServerParameters(
                RebecInstantiationMapping.getInstance().getRebecReactiveClassType(receiver),
                serverName
        );
        HashMap<String, Variable> callParameters = new HashMap<>();
        for (int i = 0; i < serverParams.size(); i++) {
            Variable paramValue = evaluatorVisitor.visit(((TermPrimary) sendStatement.getRight()).getParentSuffixPrimary().getArguments().get(i));
            paramValue.setName(serverParams.get(i).getName());
            callParameters.put(
                    serverParams.get(i).getName(),
                    paramValue
            );
        }
        return callParameters;
    }

    private void addExtractedStatement(ActorState actorState, Statement statement) {
        if (statement != null) {
            if (statement instanceof BlockStatement) {
                actorState.addStatementsToFront(((BlockStatement) statement).getStatements());
            } else {
                actorState.addStatementsToFront(List.of(statement));
            }
        }
    }

    public List<HybridState> sendStatement(ActorState actorState) {
        Cloner cloner = new Cloner();
        List<HybridState> result = new ArrayList<>();
        HybridState newHybridState = cloner.deepClone(this);
//        RunUnchangeableStatementsVisitors runner = new RunUnchangeableStatementsVisitors(actorState);
        // TODO: do it better for another type og statements
        ActorState newActorState = cloner.deepClone(actorState);
        // CHECKME: maybe shouldn't delete
        final DotPrimary sendStatement = (DotPrimary) actorState.getSigma().get(0);
        newActorState.nextStatement();

        String sender = actorState.actorName;
        String receiver = RebecInstantiationMapping.getInstance().getKnownRebecBinding(sender, ((TermPrimary) sendStatement.getLeft()).getName());
        if (receiver == null && ((TermPrimary) sendStatement.getLeft()).getName().equals("self")) {
            receiver = sender;
        }
        String serverName = ((TermPrimary) sendStatement.getRight()).getName();

        ExpressionEvaluatorVisitor evaluatorVisitor = new ExpressionEvaluatorVisitor(newActorState.getVariableValuation());
        HashMap<String, Variable> callParameters = getMessageCallParameter(receiver, serverName, evaluatorVisitor, sendStatement);

        ContinuousVariable messageArrivalTime = getDelayAfterTime(
                ((TimedRebecaParentSuffixPrimary) ((TermPrimary) sendStatement.getRight()).getParentSuffixPrimary()).getStartAfterExpression(),
                ((TimedRebecaParentSuffixPrimary) ((TermPrimary) sendStatement.getRight()).getParentSuffixPrimary()).getEndAfterExpression(),
                ((TimedRebecaParentSuffixPrimary) ((TermPrimary) sendStatement.getRight()).getParentSuffixPrimary()).getAfterExpression(),
                evaluatorVisitor
        );
        messageArrivalTime.setName("arrivalTime");
        Message message = new Message(actorState.actorName, receiver, serverName, callParameters, messageArrivalTime);
        resetResumeTime(newActorState);
        if (sender.equals(receiver)) {
            newActorState.addMessage(message);
            newHybridState.replaceActorState(newActorState);
        }
        else {
            ActorState receiverActorState = newHybridState.getActorState(receiver);
            receiverActorState.addMessage(message);
            newHybridState.replaceActorState(newActorState);
            newHybridState.replaceActorState(receiverActorState);
        }
        result.add(newHybridState);

        HybridState suspendedState = createSuspendedState(actorState);
        if (suspendedState != null) {
            result.add(suspendedState);
        }

        return result;
    }

    public List<HybridState> assignStatement(ActorState actorState) {
        Cloner cloner = new Cloner();
        List<HybridState> result = new ArrayList<>();
        HybridState newHybridState = cloner.deepClone(this);
        ActorState newActorState = cloner.deepClone(actorState);
        // CHECKME: maybe shouldn't delete
        BinaryExpression assignStatement = (BinaryExpression) newActorState.nextStatement();

        String variableName = ((TermPrimary) assignStatement.getLeft()).getName();
        Variable variableValue = new ExpressionEvaluatorVisitor(actorState.getVariableValuation()).visit(assignStatement.getRight());
        variableValue.setName(variableName);
        newActorState.updateVariable(variableValue);
        resetResumeTime(newActorState);
        newHybridState.replaceActorState(newActorState);
        result.add(newHybridState);

        HybridState suspendedState = createSuspendedState(actorState);
        if (suspendedState != null) {
            result.add(suspendedState);
        }

        return result;
    }

    public List<HybridState> delayStatement(SoftwareState softwareState) {
        Cloner cloner = new Cloner();
        List<HybridState> result = new ArrayList<>();
        HybridState newHybridState = cloner.deepClone(this);
        SoftwareState newSoftwareState = cloner.deepClone(softwareState);
        // CHECKME: maybe shouldn't delete
        final TermPrimary delayStatement = (TermPrimary) softwareState.getSigma().get(0);
        newSoftwareState.nextStatement();

        ExpressionEvaluatorVisitor evaluatorVisitor = new ExpressionEvaluatorVisitor(newSoftwareState.getVariableValuation());
        ContinuousVariable delayTime = getDelayAfterTime(
                delayStatement.getParentSuffixPrimary().getArguments().get(0),
                delayStatement.getParentSuffixPrimary().getArguments().get(1),
                delayStatement.getParentSuffixPrimary().getArguments().get(0),
                evaluatorVisitor
        );
        delayTime.setName("resumeTime");

        newSoftwareState.setResumeTime(delayTime);
        newHybridState.replaceActorState(newSoftwareState);
        result.add(newHybridState);

        HybridState suspendedState = createSuspendedState(softwareState);
        if (suspendedState != null) {
            result.add(suspendedState);
        }
        return result;
    }

    public List<HybridState> ifStatement(ActorState actorState) {
        Cloner cloner = new Cloner();
        List<HybridState> result = new ArrayList<>();
        HybridState newHybridState = cloner.deepClone(this);
        ActorState newActorState = cloner.deepClone(actorState);
        // CHECKME: maybe shouldn't delete
        ConditionalStatement conditionalStatement = (ConditionalStatement) actorState.getSigma().get(0);
        newActorState.nextStatement();
        ExpressionEvaluatorVisitor expressionEvaluatorVisitor = new ExpressionEvaluatorVisitor(actorState.getVariableValuation());
        DiscreteBoolVariable conditionResult = (DiscreteBoolVariable) expressionEvaluatorVisitor.visit(conditionalStatement.getCondition());

        if (conditionResult.getDefinite()) {
            if (conditionResult.getValue()) {
                addExtractedStatement(newActorState, conditionalStatement.getStatement());
            }
            else {
                addExtractedStatement(newActorState, conditionalStatement.getElseStatement());
            }
            resetResumeTime(newActorState);
            newHybridState.replaceActorState(newActorState);
            result.add(newHybridState);
        } else {
            addExtractedStatement(newActorState, conditionalStatement.getStatement());
            ActorState newActorState2 = cloner.deepClone(actorState);
            newActorState2.nextStatement();
            addExtractedStatement(newActorState2, conditionalStatement.getElseStatement());
            resetResumeTime(newActorState);
            resetResumeTime(newActorState2);
            newHybridState.replaceActorState(newActorState);
            HybridState newHybridState2 = cloner.deepClone(newHybridState);
            newHybridState2.replaceActorState(newActorState2);
            result.add(newHybridState);
            result.add(newHybridState2);
        }

        HybridState suspendedState = createSuspendedState(actorState);
        if (suspendedState != null) {
            result.add(suspendedState);
        }

        return result;
    }

    public List<HybridState> setModeStatement(PhysicalState physicalState) {
        Cloner cloner = new Cloner();
        List<HybridState> result = new ArrayList<>();
        HybridState newHybridState = cloner.deepClone(this);
        PhysicalState newPhysicalState = cloner.deepClone(physicalState);
        // CHECKME: maybe shouldn't delete
        final TermPrimary setModeStatement = (TermPrimary) physicalState.getSigma().get(0);

        newPhysicalState.nextStatement();

        String mode = ((TermPrimary) setModeStatement.getParentSuffixPrimary().getArguments().get(0)).getName();
        newPhysicalState.setMode(mode);
        newPhysicalState.setLastTimeModeChangedLowerBound(globalTime.getLowerBound());
        newHybridState.replaceActorState(newPhysicalState);
        result.add(newHybridState);
        return result;
    }

    public ContinuousVariable getGlobalTime() {
        return this.globalTime;
    }

    public ActorState getActorState(String actorName) {
        SoftwareState softwareState = softwareStates.get(actorName);
        return softwareState != null ? softwareState : physicalStates.get(actorName);
    }

    public List<Set<String>> getGlobalStateModes() {
        List<Set<String>> globalStateModes = new ArrayList<>();

        for (Map.Entry<String, PhysicalState> entry : physicalStates.entrySet()) {
            String key = entry.getKey();
            PhysicalState value = entry.getValue();

            if (!("none".equals(value.getMode()))) {
                Set<String> new_set = new HashSet<>();
                new_set.add(key);
                new_set.add(value.getMode());
                globalStateModes.add(new_set);

            }
        }
        return  globalStateModes;
    }

    public double[] getIntervals(String[] ODEs) {
        ArrayList<Double> intervalsList = new ArrayList<>();
        for (String ODE : ODEs){
            String[] components = extractVariableNames(ODE);
            String physicalClassName = components[0], odeVariableName = components[1];

            for (Map.Entry<String, PhysicalState> entry : physicalStates.entrySet()) {
                PhysicalState it = entry.getValue();
                String itName = entry.getKey();

                if (physicalClassName.equals(itName)) {
                    for (Map.Entry<String, Variable> VariablesValuation : it.getVariablesValuation().entrySet()) {
                        String variable = VariablesValuation.getKey();
                        Variable valuation = VariablesValuation.getValue();

                        if(odeVariableName.equals(variable)) {
                            intervalsList.add(((IntervalRealVariable)valuation).getLowerBound());
                            intervalsList.add(((IntervalRealVariable)valuation).getUpperBound());
                        }
                    }
                }
            }
        }

        double[] intervalsArray = new double[intervalsList.size()];
        for (int i = 0; i < intervalsList.size(); i++)
            intervalsArray[i] = intervalsList.get(i);
        return intervalsArray;
    }

    public static String[] extractVariableNames(String input) {
        String[] result = new String[2];
        String[] firstSplit = input.split("_");
        result[0] = firstSplit[0];
        String secondPart = firstSplit[1].replace("'", "").split("=")[0];
        result[1] = secondPart;

        return result;
    }

    public String getParentHash() {
        return parentHash;
    }

    public void setParentHash(String parentHash) {
        this.parentHash = parentHash;
    }

    public double[] getEvents(double globalTimeLowerBound, double timeInterval) {

        ArrayList<Double> resumeTimes = getSoftwareStatesResumeTimes();
        ArrayList<Double> arrivalTimes = getMessageArrivalTimes();

        ArrayList<Double> combinedList = new ArrayList<>(resumeTimes);
//        combinedList.add(globalTimeLowerBound + timeInterval);
//        combinedList.add(globalTimeUpperBound + timeInterval);
        combinedList.addAll(arrivalTimes);
        combinedList.removeIf(value -> value <= globalTimeLowerBound);

        double[] Events = combinedList.stream().mapToDouble(Double::doubleValue).toArray();
        Arrays.sort(Events);

        return Events;
    }

    private ArrayList<Double> getSoftwareStatesResumeTimes() {
        ArrayList<Double> resumeTimes = new ArrayList<>();
        for (SoftwareState softwareState : softwareStates.values()) {
            resumeTimes.add(softwareState.getResumeTime().getLowerBound().doubleValue());
            resumeTimes.add(softwareState.getResumeTime().getUpperBound().doubleValue());
        }

        return resumeTimes;
    }

    private ArrayList<Double> getMessageArrivalTimes() {
        ArrayList<Double> arrivalTimes = new ArrayList<>();
        for (SoftwareState softwareState : softwareStates.values()) {
            for (Message message : softwareState.messageBag) {
                arrivalTimes.add(message.getArrivalTime().getLowerBound().doubleValue());
                arrivalTimes.add(message.getArrivalTime().getUpperBound().doubleValue());
            }
        }

        return arrivalTimes;
    }

    public void setPhysicalStates(HashMap<String, PhysicalState> physicalStates) {
        this.physicalStates = physicalStates;
    }

    public void setSoftwareStates(HashMap<String, SoftwareState> softwareStates) {
        this.softwareStates = softwareStates;
    }

    public void updateGlobalTime(double lowerBound, double upperBound) {
        this.globalTime.setLowerBound(lowerBound);
        this.globalTime.setUpperBound(upperBound);
    }
}
