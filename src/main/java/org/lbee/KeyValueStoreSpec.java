package org.lbee;

import org.lbee.instrumentation.BehaviorRecorder;
import org.lbee.instrumentation.VirtualField;

public interface KeyValueStoreSpec {

    BehaviorRecorder spec();
    VirtualField specTx();
    VirtualField specStore();
    VirtualField specMissed();
    VirtualField specWritten();
    VirtualField specSnapshotStore();

}
