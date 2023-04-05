package org.lbee;

import org.lbee.instrumentation.TraceInstrumentation;
import org.lbee.instrumentation.TraceProducerException;

public class Helpers {

    public static boolean tryCommit(TraceInstrumentation traceInstrumentation) {
        try {
            traceInstrumentation.commitChanges();
            return true;
        } catch (TraceProducerException e) {
            System.out.println(e.toString());
            e.printStackTrace();
            return false;
        }
    }

}
