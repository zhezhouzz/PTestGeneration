# P Test Generation

# Install

The easiest way to install the dependencies is via [OPAM](https://opam.ocaml.org/doc/Install.html).

```
  opam init --auto-setup
  opam update
  opam switch create PTest --package=ocaml-base-compiler.5.3.0,ocaml-options-vanilla.1
  eval $(opam env)
  opam install dune core core_unix yojson conf-c++ conf-python qcheck ocolor dolog ocamlbuild z3 ppx_deriving_yojson menhirLib menhir ppx_deriving ppx_here spectrum ppx_sexp_conv
```

Then compile this repo:

```
    dune build
```

# Run Synthesizer

```
dune exec -- bin/main.exe syn [P type and event definition file] [Specification file] [Output file]
```

For example, the following command read `head.p` and `spec.p`, then write the synthesized P client machine into file `NewClient.p`.

```
dune exec -- bin/main.exe syn
/Users/zhezzhou/workspace/amazon_ws/src/TestExamples-PTestGeneration/Examples/ClockBoundFormalModels/head.p
/Users/zhezzhou/workspace/amazon_ws/src/TestExamples-PTestGeneration/Examples/ClockBoundFormalModels/spec.p
/Users/zhezzhou/workspace/amazon_ws/src/TestExamples-PTestGeneration/ClockBoundFormalModels/ClockBound/PSyn/NewClient.p
```

The generated client machines should be setup correctly by test driver machines:
- The test driver needs to create the client machine.
- The test driver needs to set the global param variable `creator` as itself.
- The test driver needs to set the global param variable `destMachines` as the machines client can send message.
- The client machine will send `eGClientDone` event to the test driver, which should be handled.

For example,

```
    destMachines = default(set[machine]);
    destMachines = ...;
    creator = this;
    new GeneratedClient();
```

# Specification Language

- Set up the events should be recorded in history traces.
```
visible EVENT_NAME, ...;
```

- There are two kinds of specifications.
  + Payload generator specification.
```
prop NAME on EVENT_NAME {
    return P_EXPR;
}
```
  + FOL constraint on event accorrding to the history trace.
```
prop NAME on EVENT_NAME do e with FOL ;
```

- Synthesize client according to given requirest number bound and specifications.
```
syn CLIENT_NAME on
(EVENT_NAME = INT,
 ...
) with
SPEC_NAME, ...;
```

More examples can be found under `Examples` folder in the internal repo `TestExamples-PTestGeneration`.

# Run Benchmark

we provide script to run benchmarks in the internal `TestExamples-PTestGeneration` repo.

```
    python3 script/syn.py              // synthesize clients
    python3 script/runp.py             // run p compiler and checker
    python3 script/analysis.py         // analysis result
```

The file `script/common.py` stores the meta information of benchmarks, includes the path to benchmarks directory (`prefix`), path to each benchmark (`benchmarks`), default test iterations (`test_num`) and the map of client names to the corresponding test case name used in p checking (`client_name_to_tc`).

We can run specific benchmark or specfic client machine use the following command:
```
    python3 script/runp.py -b ClockBoundFormalModels
    python3 script/runp.py -b ClockBoundFormalModels -n GClientSame
```

The generated code are in `PSyn` folder, structured as following:

```
PSyn
├── Library.p (optional)
├── NewClient.p
├── SynDriver.p
```

+ `NewClient.p`: output of synthesizer.
+ `Library.p`: auxiliary functions used by synthesized client machines in `SynClient.p`.
+ `SynDriver.p`: test driver and script for synthesized client machines.


# Notes

Note that `C#` functions cannot be invoked in global P functions, thus we need to add some global functions into synthesized client manually.
- `record_gen` and `key_gen` in `S3IndexBrickManagerPModels/PSyn/Library.p`.
- `wait_time_gen` and `key_gen` in `ClockBoundFormalModels/ClockBound/PSyn/Library.p`.

The `ChainReplication` requires the client machine to send back a `Ack` message after intialization, which cannot be synthesized. For now, just add one event handler in the `Init` state.
```
start state Init {
    entry {
    ...
    }
    // Add the following handler
    on eNotifyNewHeadTail do (input: (master: Master, h : Replicate, t: Replicate)) {
      record_eNotifyNewHeadTail_seq(this, this, input);
      send input.master, eAck, this as machine;
      goto Main;
    }
  }
```

