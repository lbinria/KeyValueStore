import os
import time
import signal
from subprocess import Popen

def run():
    impl_process = Popen([
        "/usr/lib/jvm/jdk-19/bin/java",
        "-jar",
        "target/KeyValueStore-1.0-jar-with-dependencies.jar"
        ])

    # Wait implementation is terminated
    impl_process.wait()
    impl_process.terminate()

if __name__ == "__main__":
    run()