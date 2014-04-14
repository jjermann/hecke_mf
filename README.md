Hecke modular forms
===================

An implementation for sage:
---------------------------

  * Trac ticket: http://trac.sagemath.org/ticket/16134

  * At the moment: Only support for forms with respect to
    the full Hecke triangle group for `n=3, 4, 5, ...`

  * The ring of modular forms as a commutative algebra.

  * The space of modular forms of given weight as a module.

  * Supported analytic types (implemented as an extended `FiniteLatticePoset` class):
      * meromorphic
      * weakly holomorphic
      * holomorphic
      * cuspidal
      * Support for quasi modular forms for all of the above types

  * Exact calculations (no precision argument is required).

    The calculations are based on the three generators of the
    graded algebra: `x=f_rho`, `y=f_i`, `z=E2`.
    Every form has a representation as a rational function in
    `x`, `y`, `z`.

    Checks are performed to determine the analytic type of elements.

  * Fourier expansion with (exact) coefficients in `Frac(R)[d]`,
    where `R` is some base ring (e.g. `ZZ`) and `d` is a
    formal parameter corresponding to a (possibly) transcendental
    number which turns up in the Fourier expansion.  

    It is also possible to evaluate `d` numerically.

    The Fourier expansion is (should be) determined exactly
    with the specified precision.

  * For arithmetic groups the `d` is calculated exactly.

  * Evaluation of elements, viewed as functions from the
    upper half plane. This uses the modularity properties for
    faster/more precise evaluation. However the precision of
    the result depends on the precision specified for the
    Fourier expansion.

  * Calculation of derivatives and serre derivatives.

  * Basis for weakly holomorphic modular forms.

  * Faber polynomials.

  * (Exactly) determine weakly holomorphic modular forms
    by their initial Fourier coefficients.

  * Dimension and basis for holomorphic or cuspidal (quasi) modular forms.

  * Coordinate vectors for holomorphic modular forms and cusp forms.

  * Subspaces (with respect to a basis) for ambient spaces
    that support coordinate vectors, together with coordinate
    vectors for subspaces.

  * Complete documentation of all functions and methods.

  * Complete doctests of all functions and methods, except for:
      * analytic_type.py


Redesign/refactoring idea:
--------------------------

  * Forms spaces/rings with reduced coefficient rings:
      * That would require a lot of work (sigh)...
      * Initialize everything with an optional "fix_d" parameter
        (maybe even with a "set_d" parameter).
      * In case that parameter is set the corresponding rings are changed:
        base ring, polynomial ring, fraction field, coefficient ring
      * Make the MFSeriesConstructor part of the abstract ring?
        In particular: all functions which have a fix_d/set_d parameter
        would now query it from the space instead.
      * For arithmetic groups fix_d could be set by default.


Future ideas (hard):
--------------------

  * Support for general triangle groups
  * Support for "congruence" subgroups
