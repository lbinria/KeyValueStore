package org.lbee;

import org.lbee.instrumentation.TraceInstrumentation;
import org.lbee.instrumentation.VirtualField;

public interface KeyValueStoreSpec {

    TraceInstrumentation spec();
    VirtualField specTx();
    VirtualField specStore();
    VirtualField specMissed();
    VirtualField specWritten();
    VirtualField specSnapshotStore();

}
