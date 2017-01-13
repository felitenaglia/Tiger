# Tiger

Assignment at university. Course: Compilers. Year: 2014.

Based on the book "Modern compiler implementation in ML" by Andrew Appel

## Target architecture

The target architecture of this compiler is `ARMv7A`. It also allows cross-compiling (flag `-cc`).

## Requirements

If it is run on an ARMv7A microprocessor, only `gcc` is required and no flags are needed. Otherwise, it requires `arm-linux-gnueabi-gcc` and the flag `-cc` has to be present. 
