# boomerang_search
This repo contains the code for paper 'SAT-aided Automatic Search of Boomerang Distinguishers for ARX Ciphers (Long Paper)'.

```
git clone https://github.com/google/or-tools.git src/3rd/or-tools
mkdir build
cd build
cmake ..
make

```

The 'arxtools_lea_switch_model' folder contains the ARXtools model for computing the probability of LEA. 'test_constr.c' is a modified version of the original 'constraints.c' to support the large word size of LEA.

