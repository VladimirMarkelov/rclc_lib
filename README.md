## What is it

Mathematical expression evaluation library with big integers, floats, common fractions, and complex numbers support.
The library is used by the project [RionaCalc](https://github.com/VladimirMarkelov/rclc)

## Features

* Automatic selection of more appropriate argument type for a function: e.g, `sqrt(-4)` converts float number `-4` into complex one `-4+0i` and then calculates the result `0+2i`. The same is true for calculating logarithm for negative float numbers, and acos and asin for argument greater than `1.0`
* Automatic adding multiplication sign where it is omitted: e.g, `(1+2)(2+9)` is calculated as `(1+2)*(2+9)`
* Functions with a single-value argument do not require to enclose its argument into brackets: e.g, `sin cos 2` is calculated as `sin(cos(2))`
* The final closing brackets can be omitted: e.g, `(1+2)*(2+9` is the same as `(1+2)*(2+9)`
* Trigonometric functions work with radians and degrees. Bare numbers are treated as radians, degrees requires one or three suffixes. Two degrees formats: `20d30m50s` or `20°30'50"`. Minutes and seconds can be omitted, in this case degrees can be float number like `30.25d`. So, `sin(pi/2)` == `sin(90°)`
* Every number can include group separator `_` for readability - it is very useful when using big integers. `3_000.90_23` == `3000.9023`
* Both `.` and `,` are treated as decimal separators
* Function argument separator is `;`. If a function receives more arguments than it requires, the trailing arguments are dropped: e.g, `sqrt(11;12;13)` is the same as `sqrt(11)`
* Regular fractions use `\` to separate its parts. They can be written with integer part or only with numerator and denominator, e.g `1\1\10` == `11\10`
* Two complex numbers formats: with marker at the end or in the middle. E.g, `1+2i` == `1+i2`. In addition, `j` can be used instead of `i` - but the calculator outputs always with `i`
* Hexadecimal(starts with `0x`), octal(starts with `0o`), and binary(starts with `0b`) numbers
