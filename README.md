# KeyValueStore

An implementation of KVS specification.
https://github.com/tlaplus/Examples/tree/master/specifications/KeyValueStore

## Prerequisite

 - Java >= 17.0.6
 - Apache maven >= 3.6.3
 - Python >= 3.9.12


Install trace_validation_tools scripts.

## Run

Run implementation alone: 

`python run_impl.py`

Run implementation following by trace validation: 

`python trace_validation_pipeline.py`

## Project structure

spec/ directory contains KVS TLA+ specification and KVS specification for trace validation.

src/ directory contains a java implementation of KVS spec.

## Some words about trace validation