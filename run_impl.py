from subprocess import Popen

def run():
    impl_process = Popen([
        "java",
        "-cp",
        "target/KeyValueStore-1.2-jar-with-dependencies.jar",
        "org.lbee.start.MainSimple"
        ])

    # Wait implementation is terminated
    impl_process.wait()
    impl_process.terminate()

if __name__ == "__main__":
    run()