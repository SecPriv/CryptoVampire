We are still only concerned with the indistinguishability crate.

The backed for protocols supporting memory cell is in, now we need to do the front end.

I thus want you to do 3 things:
0. Familiarize yourself with how memory cell works.
1. add scheme bindings to be able to let the user declare assignements to memory cell in protocols
2. convert `/home/simon/squirrel-prover/examples/stateful/running-ex.sp` to the scheme fromat cryptovampire uses 
3. fix bugs potentially introduced in step 1, report (to a markdown file) bugs comming from deeper in cryptovampire 

Here comes more details about each tasks:

# Task 1.
You can take inspiration from `input` folder. You may have to add methods to the `Problem` type.
Please comment all user facing changes

I also want you to adapt the files in `crates/indistinguishability/scheme/libs` if necessary so the that the user experience remains accpetable.

# Task 2.
Put the new scheme files in `/home/simon/ccsa/cryptovampire/crates/indistinguishability/tests/passing`.

Take inspiration from all the protocols in `/home/simon/ccsa/cryptovampire/crates/indistinguishability/tests/passing` most of them are more or less straight transaltion from other protocols from `/home/simon/squirrel-prover/examples`.

Note that I don't expect these new example to be provable. They are simply a pretext for an intragration test of the memory cell backend.
To help thing fail faster, you can add `(config.set_vampire_timeout pbl (b.mult->duration scale-timeout (b.string->duration "150ms")))`.

# Task 3.
The intergration test is to run the files made in task 2. Beware that they might take a long time or loop.

Your task here is to fix any bug introduced because of Task 1 and report all those comming from somewhere else so that I can take a look at them later.