from subprocess import Popen

def run():
    impl_process = Popen([
        "java",
        "-jar",
        "target/KeyValueStore-1.1-jar-with-dependencies.jar"
        ])

    # Wait implementation is terminated
    impl_process.wait()
    impl_process.terminate()

if __name__ == "__main__":
    run()