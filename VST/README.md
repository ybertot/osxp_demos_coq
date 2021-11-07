# Illustration of C code verification

The code is in the master of
[the cverified/cbench-vst repository](https://github.com/cverified/cbench-vst).
To run it, it has been necessary to ensure that the
packages `coq-vst`, `coq-flocq`, and `coq-gappa` were `opam`-installed.

After cloning the repository, I needed to remove some of the files that were
actually meant to be generated by some of the compcert by-products.

```
cd cbench-vst/sqrt
rm sqrt1.v sqrt3.v
make
```

The C code that is proved correct is visible in file `sqrt1.c` and is
repeated here:

```C
float
sqrt_newton(float x)
{
  float y, z;

  if (x <= 0)
    return 0;
  y = x >= 1 ? x : 1;
  do {
    z = y;
    y = (z + x/z)/2;
  } while (y < z);
  return y;
}
```

The main theorem is `body_sqrt_newton2`, it relies on the following
specification:

```Coq
Definition sqrt_newton_spec2 :=
   DECLARE _sqrt_newton
   WITH x: float32
   PRE [ tfloat ]
       PROP ( powerRZ 2 (-122) <= f2real x < powerRZ 2 125 )
       PARAMS (Vsingle x)
       SEP ()
    POST [ tfloat ]
       PROP (Rabs (f2real (fsqrt x) - sqrt (f2real x)) <=
                       3 / (powerRZ 2 23) * sqrt (f2real x))
       RETURN (Vsingle (fsqrt x))
       SEP ().
```

Two important parts are added with respect to unverified C code:

```
PRE
  [tfloat]
  PROP (powerRZ (2 (-122) <= f2real x < powerRZ 2 125))
  PARAMS (Vsingle x)
  SEP ()
```
This expresses that the type of the input is a `tfloat` (the Coq name for the
type of C floating point numbers)
<span style="color:red">and more importantly</span>,
that correct behavior is only guaranteed if the value of x is
larger than `2 ^ (-122)` and smaller than `2 ^ 125`.

The second important part is the guarantees that have been proved about
the results of execution.
```
    POST [ tfloat ]
       PROP (Rabs (f2real (fsqrt x) - sqrt (f2real x)) <=
                       3 / (powerRZ 2 23) * sqrt (f2real x))
       RETURN (Vsingle (fsqrt x))
```
This states that the result also has the C type `float` but it also
indicates that the value computed as a result is not further than
`sqrt(x) * 3 / (2 ^ 23)` from `sqrt(x)`.

The code actually has better properties (especially considering the range on
which the function behaves correctly), but this what has been proved.