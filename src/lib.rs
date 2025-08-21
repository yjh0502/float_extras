extern crate libc;

#[allow(dead_code)]
mod cmath {
    use libc::{c_double, c_int};

    #[link(name = "m")]
    unsafe extern "C" {
        pub fn frexp(n: c_double, value: &mut c_int) -> c_double;
        pub fn ldexp(x: c_double, n: c_int) -> c_double;
        pub fn modf(x: c_double, iptr: &mut c_double) -> c_double;
        pub fn ilogb(n: c_double) -> c_int;
        pub fn logb(n: c_double) -> c_double;
        pub fn scalbn(x: c_double, n: c_int) -> c_double;

        pub fn erf(n: c_double) -> c_double;
        pub fn erfc(n: c_double) -> c_double;
        pub fn tgamma(n: c_double) -> c_double;
        pub fn lgamma(n: c_double) -> c_double;

        pub fn fmod(a: c_double, b: c_double) -> c_double;
        pub fn lround(x: c_double) -> c_int;
        // need longlong: llround
        // need fenv.h: rint, lrint, llrint, nearbyint
        pub fn remainder(a: c_double, b: c_double) -> c_double;
        pub fn remquo(x: c_double, y: c_double, quot: &mut c_int) -> c_double;

        pub fn copysign(x: c_double, y: c_double) -> c_double;
        pub fn nextafter(x: c_double, y: c_double) -> c_double;
        // need long_double: nexttoward

        pub fn fdim(a: c_double, b: c_double) -> c_double;
        pub fn fma(x: c_double, y: c_double, z: c_double) -> c_double;
    }
}

pub mod f64 {
    use super::cmath;
    use libc::c_int;

    /// frexp is used to split the number x into a normalized fraction and an exponent
    /// which is stored in exp.
    pub fn frexp(x: f64) -> (f64, isize) {
        let mut n: c_int = 0;
        let f = unsafe { cmath::frexp(x, &mut n) };
        (f, n as isize)
    }
    /// ldexp returns the result of multiplying the floating-point number x by 2 raised to
    /// the power exp.
    pub fn ldexp(x: f64, exp: isize) -> f64 {
        unsafe { cmath::ldexp(x, exp as i32) }
    }
    /// modf breaks the argument x into an integral part and a fractional part, each
    /// of which has the same sign as x.
    pub fn modf(x: f64) -> (f64, f64) {
        let mut i: f64 = 0.;
        let f = unsafe { cmath::modf(x, &mut i) };
        (i, f)
    }
    /// iligb returns the exponent part of their argument as a signed integer.
    pub fn ilogb(n: f64) -> isize {
        (unsafe { cmath::ilogb(n) }) as isize
    }
    /// logb extracts the exponent from the internal floating-point
    /// representation of x and return it as a floating-point value.
    pub fn logb(x: f64) -> f64 {
        unsafe { cmath::logb(x) }
    }
    /// scalbn multiplies their first argument x by FLT_RADIX (probably 2) to the power of
    /// exp, that is:
    /// ```text
    /// x * FLT_RADIX ** exp
    /// ```
    pub fn scalbn(x: f64, exp: isize) -> f64 {
        unsafe { cmath::scalbn(x, exp as c_int) }
    }

    /// erf returns the error function of x, defined as
    /// ```text
    /// erf(x) = 2/sqrt(pi)* integral from 0 to x of exp(-t*t) dt
    /// ```
    pub fn erf(x: f64) -> f64 {
        unsafe { cmath::erf(x) }
    }
    /// erfc returns the complementary error function of x, that is, 1.0 - erf(x).
    pub fn erfc(x: f64) -> f64 {
        unsafe { cmath::erfc(x) }
    }

    /// tgamma calculates the Gamma function of x.
    ///
    /// The Gamma function is defined by
    ///
    /// ```text
    /// Gamma(x) = integral from 0 to infinity of t^(x-1) e^-t dt
    /// ```
    /// It is defined for every real number except for nonpositive integers.  For nonnegative
    /// integral m one has
    ///
    /// ```text
    /// Gamma(m+1) = m!
    /// ```
    /// and, more generally, for all x:
    ///
    /// ```text
    /// Gamma(x+1) = x * Gamma(x)
    /// ```
    ///
    /// Furthermore, the following is valid for all values of x outside the poles:
    ///
    /// ```text
    /// Gamma(x) * Gamma(1 - x) = PI / sin(PI * x)
    /// ```
    pub fn tgamma(x: f64) -> f64 {
        unsafe { cmath::tgamma(x) }
    }
    /// lgamma returns the natural logarithm of the absolute value of the Gamma function.
    pub fn lgamma(x: f64) -> f64 {
        unsafe { cmath::lgamma(x) }
    }

    /// fmod computes the floating-point remainder of dividing x by y.  The return
    /// value is x - n * y, where n is the quotient of x / y, rounded toward zero to an integer.
    pub fn fmod(x: f64, y: f64) -> f64 {
        unsafe { cmath::fmod(x, y) }
    }
    /// lround rounds their argument to the nearest integer value, rounding away from zero.
    pub fn lround(x: f64) -> isize {
        (unsafe { cmath::lround(x) }) as isize
    }
    /// remainder compute the remainder of dividing x by y. The return value is x-n*y, where
    /// n is the value x / y, rounded to the nearest integer. If the absolute value of x-n*y is
    /// 0.5, n is chosen to be even.
    pub fn remainder(x: f64, y: f64) -> f64 {
        unsafe { cmath::remainder(x, y) }
    }
    /// remquo computes the remainder and part of the quotient upon division of x by y.
    pub fn remquo(x: f64, y: f64) -> (isize, f64) {
        let mut quot: c_int = 0;
        let rem = unsafe { cmath::remquo(x, y, &mut quot) };
        (quot as isize, rem)
    }

    /// copysign returns a value whose absolute value matches that of x, but whose sign bit
    /// matches that of y.
    pub fn copysign(x: f64, y: f64) -> f64 {
        unsafe { cmath::copysign(x, y) }
    }
    /// nextafter returns the next representable floating-point value following x in the
    /// direction of y. If y is less than x, these functions will return the largest representable
    /// number less than x.
    pub fn nextafter(x: f64, y: f64) -> f64 {
        unsafe { cmath::nextafter(x, y) }
    }

    /// fdim returns the positive difference, max(x-y,0), between their arguments.
    pub fn fdim(x: f64, y: f64) -> f64 {
        unsafe { cmath::fdim(x, y) }
    }
    /// fma computes x * y + z. The result is rounded as one ternary operation
    /// according to the current rounding mode.
    pub fn fma(x: f64, y: f64, z: f64) -> f64 {
        unsafe { cmath::fma(x, y, z) }
    }
}

#[cfg(test)]
mod tests {
    use super::f64::*;

    #[test]
    fn smoke_test() {
        frexp(0.);
        ldexp(0., 0);
        modf(0.);
        ilogb(0.);
        logb(0.);
        scalbn(0., 0);

        erf(0.);
        erfc(0.);
        tgamma(0.);
        lgamma(0.);
        lround(0.);
        remainder(0., 0.);
        remquo(0., 0.);

        copysign(0., 0.);
        nextafter(0., 0.);

        fdim(0., 0.);
        fma(0., 0., 0.);
    }
}
