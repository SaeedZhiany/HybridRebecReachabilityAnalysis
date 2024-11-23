package sos;

import stateSpace.HybridState;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class NonTimeProgressSOSExecutor {


    private final List<AbstractSOSExecutor> sosExecutors = new ArrayList<AbstractSOSExecutor>() {{
        add(new AssignmentStatementSOSExecutor());
        add(new DelaySOSExecuter());
        add(new TakeMessageSOSExecutor());
        add(new SendStatementSOSExecuter());
        add(new IfStatementSOSExecutor());
        add(new SetModeSOSExecutor());
    }};

    public List<HybridState> generateNextStates(HybridState hybridState, boolean returnTotalStates) {
        final Map<String, HybridState> totalStates = new HashMap<>();
        final Map<String, HybridState> lastStateResults = new HashMap<>();
        Map<String, HybridState> nextRoundStates = new HashMap<>();
        Map<String, HybridState> currentRoundStates = new HashMap<>();

        hybridState.updateHash();
        currentRoundStates.put(hybridState.getHash(), hybridState);
        boolean isProcessEnd = false;
        while (!isProcessEnd) {
            isProcessEnd = true;
            for (Map.Entry<String, HybridState> entry : currentRoundStates.entrySet()) {
                boolean isStateProcessEnd = true;
                for (AbstractSOSExecutor executor : sosExecutors) {
                    if (executor.isApplicable(entry.getValue())) {
                        isProcessEnd = false;
                        isStateProcessEnd = false;
                        List<HybridState> generatedHybridStates = executor.execute(entry.getValue());
                        for (HybridState generatedHybridState : generatedHybridStates) {
                            generatedHybridState.updateHash();
                            generatedHybridState.setParentHash(entry.getKey());
                            nextRoundStates.put(generatedHybridState.getHash(), generatedHybridState);
                        }
                    }
                }
                if (isStateProcessEnd) {
                    lastStateResults.put(entry.getKey(), entry.getValue());
                }
            }
            totalStates.putAll(currentRoundStates);
            currentRoundStates = new HashMap<>(nextRoundStates);
            nextRoundStates.clear();
        }
        if (returnTotalStates)
            return new ArrayList<>(totalStates.values());

        for (Map.Entry<String, HybridState> entry : lastStateResults.entrySet()) {
            if (!entry.getValue().getHash().equals(hybridState.getHash()))
                entry.getValue().setParentHash(hybridState.getHash());
        }
        return new ArrayList<>(lastStateResults.values());
    }
}
