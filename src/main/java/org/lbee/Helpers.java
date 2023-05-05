package org.lbee;

import org.lbee.instrumentation.clock.LogicalClock;

public class Helpers {

    private static LogicalClock clock;

    public static LogicalClock getClock() {
        if (clock == null)
            clock = new LogicalClock();

        return clock;
    }

}
