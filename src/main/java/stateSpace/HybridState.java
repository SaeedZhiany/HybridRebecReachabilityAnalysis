package stateSpace;

import javax.annotation.Nonnull;
import java.lang.StringBuilder;
import java.util.HashMap;
import java.util.List;

import utils.StringSHA256;
import dataStructure.ContinuousVariable;

public class HybridState {

    // CHECKME: should global time be non-null?
    @Nonnull
    private ContinuousVariable globalTime;
    @Nonnull
    private HashMap<String, SoftwareState> softwareStates;
    @Nonnull
    private HashMap<String, PhysicalState> physicalStates;
    @Nonnull
    private CANNetworkState CANNetworkState;
    @Nonnull
    private String hashString;

    public HybridState() {
        // FIXME: is this the correct way to initialize globalTime?
        // ContinuousVariable globalTime = new ContinuousVariable("globalTime");
        this(new ContinuousVariable("globalTime"), new HashMap<>(), new HashMap<>(), new CANNetworkState());
    }

    public HybridState(HybridState hybridState) {
        // CHECKME: aren't this attributes private?
        this(hybridState.globalTime, hybridState.softwareStates, hybridState.physicalStates, hybridState.CANNetworkState);
    }

    private HybridState(
            @Nonnull ContinuousVariable globalTime,
            @Nonnull HashMap<String, SoftwareState> softwareStates,
            @Nonnull HashMap<String, PhysicalState> physicalStates,
            @Nonnull stateSpace.CANNetworkState CANNetworkState
    ) {
        this.globalTime = globalTime;
        this.softwareStates = softwareStates;
        this.physicalStates = physicalStates;
        this.CANNetworkState = CANNetworkState;
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

        stringBuilder.append(globalTime.toString());

        for (SoftwareState softwareState : softwareStates.values()) {
            stringBuilder.append(softwareState.toString());
            stringBuilder.append(";");
        }
        for (PhysicalState physicalState : physicalStates.values()) {
            stringBuilder.append(physicalState.toString());
            stringBuilder.append(";");
        }
        // stringBuilder.append(CANNetworkState.toString());
        return stringBuilder.toString();
    }

    // CHECKME: when should we call this method?
    private String updateHash() throws Exception {
        return StringSHA256.hashString(this.toString());
    }

    private String getHash() {
        return this.hashString;
    }

    public HashMap<String, PhysicalState> getPhysicalStates() {
        return this.physicalStates;
    }

    public HashMap<String, SoftwareState> getSoftwareStates() {
        return this.softwareStates;
    }

    // CHECKME: check conditions
    public boolean isSuspended(ContinuousVariable resumeTime) {
        if ((resumeTime.getLowerBound().compareTo(this.globalTime.getLowerBound()) == 0) &&
                (resumeTime.getUpperBound().compareTo(this.globalTime.getUpperBound()) >= 0)) {
            return false;
        }
        return true;
    }

    public List<ActorState> takeMessage(ActorState actorState) {
        // TODO: call takeMessage method on actorState and retrieve the new actorStates
        // TODO: takeMessage method of SoftwareState can and should return multiple (at most 2?!) newSoftwareStates
        // CHECKME: does it call on correct class? (software and physical)
        return actorState.takeMessage(globalTime);
    }

    public ContinuousVariable getGlobalTime() {
        return this.globalTime;
    }
}
