r"""
Graded rings of modular forms for Hecke triangle groups

AUTHORS:

- Jonas Jermann (2013): initial version

"""

#*****************************************************************************
#       Copyright (C) 2013 Jonas Jermann <jjermann2@gmail.com>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.rings.all import ZZ, infinity, LaurentSeries, O
from sage.functions.all import exp
from sage.symbolic.all import pi, i
from sage.structure.parent_gens import localvars

from sage.structure.element import CommutativeAlgebraElement
from sage.structure.unique_representation import UniqueRepresentation
from sage.misc.cachefunc import cached_method

from constructor import rational_type, FormsSpace, FormsRing
from series_constructor import MFSeriesConstructor


# Warning: We choose CommutativeAlgebraElement because we want the
# corresponding operations (e.g. __mul__) even though the category
# (and class) of the parent is in some cases not
# CommutativeAlgebras but Modules
class FormsRingElement(CommutativeAlgebraElement, UniqueRepresentation):
    r"""
    Element of a FormsRing.
    """
    from analytic_type import AnalyticType
    AT = AnalyticType()

    @staticmethod
    def __classcall__(cls, parent, rat):
        r"""
        Return a (cached) instance with canonical parameters.
        """

        rat = parent.rat_field()(rat)
        # rat.reduce() <- maybe add this for the nonexact case

        return super(FormsRingElement,cls).__classcall__(cls, parent, rat)

    def __init__(self, parent, rat):
        r"""
        Element of a FormsRing ``parent`` corresponding to the rational
        function ``rat`` evaluated at ``x=F_rho``, ``y=F_i``, ``z=E2``
        and ``d`` by the formal parameter from ``parent.coeff_ring()``.

        The functions ``F_rho, F_i, E2`` can be obtained from
        ``self.parent().graded_ring()``.

        INPUT:
        - ``parent``  - An (non abstract) instance of ``FormsRing_abstract``.
        - ``rat``     - A rational function in ``parent.rat_field()``, the
                        fraction field of the polynomial ring in ``x,y,z,d``
                        over the base ring of ``parent``.
        
        OUTPUT:

        An element of ``parent``. If ``rat`` does not correspond to such
        an element an exception is raised.
        """

        self._rat = rat
        (elem, homo, self._weight, self._ep, self._analytic_type) = rational_type(rat, parent.hecke_n(), parent.base_ring())

        if not (
            elem and\
            self._analytic_type <= parent.analytic_type() ):
                raise Exception("{} does not correspond to an element of the {}.".format(rat, parent))

        super(FormsRingElement, self).__init__(parent)

    def _repr_(self):
        """
        Return the string representation of self.
        """
        #return "{} in {}".format(str(self._rat), self.parent())
        with localvars(self.parent()._pol_ring, "f_rho, f_i, E2, d"):
            pol_str = str(self._rat)
        return "{}".format(pol_str)

    def _latex_(self):
        r"""
        Return the LaTeX representation of ``self``.
        """
        from sage.misc.latex import latex
        with localvars(self.parent()._pol_ring, "f_rho, f_i, E2, d"):
            latex_str = latex(self._rat)
        return latex_str

    def group(self):
        r"""
        Return the (Hecke triangle) group of ``self.parent()``.
        """

        return self.parent().group()

    def hecke_n(self):
        r"""
        Return the parameter ``n`` of the (Hecke triangle) group of ``self.parent()``.
        """

        return self.parent().hecke_n()

    def base_ring(self):
        r"""
        Return base ring of ``self.parent()``.
        """

        return self.parent().base_ring()

    def coeff_ring(self):
        r"""
        Return coefficient ring of ``self``.
        """

        return self.parent().coeff_ring()

    def rat(self):
        r"""
        Return the rational function representing ``self``.
        """

        return self._rat

    def is_homogeneous(self):
        r"""
        Return whether ``self`` is homogeneous.
        """

        return self._weight != None

    def weight(self):
        r"""
        Return whether weight of ``self``.
        """

        return self._weight

    def ep(self):
        r"""
        Return whether multiplier of ``self``.
        """

        return self._ep

    def degree(self):
        r"""
        Return the degree of ``self`` in the graded ring.
        If ``self`` is not homogeneous, then ``(None, None)``
        is returned.
        """

        return (self._weight,self._ep)

    def is_modular(self):
        r"""
        Return whether ``self`` (resp. its homogeneous components)
        transform like modular forms.
        """

        return not (self.AT("quasi") <= self._analytic_type)

    def is_weakly_holomorphic(self):
        r"""
        Return whether ``self`` is weakly holomorphic
        in the sense that: ``self`` has at most a power of ``f_inf``
        in its denominator.
        """

        return self.AT("weak", "quasi") >= self._analytic_type

    def is_holomorphic(self):
        r"""
        Return whether ``self`` is holomorphic
        in the sense that the denominator of ``self``
        is constant.
        """

        return self.AT("holo", "quasi") >= self._analytic_type

    def is_cuspidal(self):
        r"""
        Return whether ``self`` is cuspidal
        in the sense that ``self`` is holomorphic and the ``f_inf``
        divides the numerator.
        """

        return self.AT("cusp", "quasi") >= self._analytic_type

    def is_zero(self):
        r"""
        Return whether ``self`` is the zero function.
        """

        return self.AT(["quasi"]) >= self._analytic_type

    def analytic_type(self):
        r"""
        Return the analytic type of ``self``.
        """

        return self._analytic_type

    def numerator(self):
        r"""
        Return the numerator of ``self``.
        I.e. the (properly reduced) new form corresponding to
        the numerator of ``self.rat()``.
        
        Note that the parent of ``self`` might (probably will) change.
        """

        res = self.parent().rat_field()(self._rat.numerator())
        # In general the numerator has a different weight than the original function...
        new_parent = self.parent().extend_type(ring=True).reduce_type(["holo", "quasi"])
        return new_parent(res)

    def denominator(self):
        r"""
        Return the denominator of ``self``.
        I.e. the (properly reduced) new form corresponding to
        the numerator of ``self.rat()``.
        
        Note that the parent of ``self`` might (probably will) change.
        """

        res = self.parent().rat_field()(self._rat.denominator())
        # In general the denominator has a different weight than the original function...
        new_parent = self.parent().extend_type(ring=True).reduce_type(["holo", "quasi"])
        return new_parent(res)

    def _add_(self,other):
        r"""
        Return the sum of ``self`` and ``other``.
        """

        return self.parent()(self._rat+other._rat)

    def _sub_(self,other):
        r"""
        Return the difference of ``self`` and ``other``.
        """

        return self.parent()(self._rat-other._rat)

#    def _rmul_(self,other):
#        res = self.parent().rat_field()(self._rat*other)
#        return self.parent()(res)
#    def _lmul_(self,other):
#        res = self.parent().rat_field()(other*self._rat)
#        return self.parent()(res)
#    def _rdiv_(self,other):
#        res = self.parent().rat_field()(self._rat/other)
#        return self.parent()(res)

    def _mul_(self,other):
        r"""
        Return the product of ``self`` and ``other``.

        Note that the parent might (probably will) change.

        If ``parent.has_reduce_hom() == True`` then
        the result is reduced to be an element of
        the corresponding forms space if possible.
        
        In particular this is the case if both ``self``
        and ``other`` are (homogeneous) elements of a
        forms space.
        """

        res = self.parent().rat_field()(self._rat*other._rat)
        new_parent = self.parent().extend_type(ring=True)
        # The product of two homogeneous elements is homogeneous
        return new_parent(res).reduce()

    def _div_(self,other):
        r"""
        Return the division of ``self`` by ``other``.

        Note that the parent might (probably will) change.

        If ``parent.has_reduce_hom() == True`` then
        the result is reduced to be an element of
        the corresponding forms space if possible.
        
        In particular this is the case if both ``self``
        and ``other`` are (homogeneous) elements of a
        forms space.
        """

        res = self.parent().rat_field()(self._rat/other._rat)
        new_parent = self.parent().extend_type("mero", ring=True)
        # The division of two homogeneous elements is homogeneous
        return new_parent(res).reduce()

    def sqrt(self):
        r"""
        Try to return the square root of ``self``.
        I.e. the element corresponding to ``sqrt(self.rat())``.

        Whether this works or not depends on whether
        ``sqrt(self.rat())`` works and coerces into
        ``self.parent().rat_field()``.

        Note that the parent might (probably will) change.

        If ``parent.has_reduce_hom() == True`` then
        the result is reduced to be an element of
        the corresponding forms space if possible.
        
        In particular this is the case if ``self``
        is a (homogeneous) element of a forms space.
        """

        res = self.parent().rat_field()(self._rat.sqrt())
        new_parent = self.parent().extend_type(ring=True)
        # The sqrt of a homogeneous element is homogeneous if it exists
        return self.parent()(res).reduce()

    #def __invert__(self,other):
    #    res = self.parent().rat_field()(1/self._rat)
    #    new_parent = self.parent().extend_type(ring=True, mero=True)
    #    return new_parent(res).reduce()

    def diff_op(self, op, new_parent=None):
        r"""
        Return the differential operator ``op`` applied to ``self``.
        If ``parent.has_reduce_hom() == True`` then the result
        is reduced to be an element of the corresponding forms
        space if possible.

        INPUT:

        - ``op``           - An element of ``self.parent().diff_alg()``.
                             I.e. an element of the algebra over ``QQ``
                             of differential operators generated
                             by ``X, Y, Z, dX, dY, DZ``, where e.g. ``X``
                             corresponds to the multiplication by ``x``
                             (resp. ``F_rho``) and ``dX`` corresponds to ``d/dx``.

                             To expect a homogeneous result after applying
                             the operator to a homogeneous element it should
                             should be homogeneous operator (with respect
                             to the the usual, special grading).

        - ``new_parent``   - Try to convert the result to the specified
                             ``new_parent``. If ``new_parent == None`` (default)
                             then the parent is extended to a
                             "quasi meromorphic" ring.
                
        OUTPUT:

        The new element.
        """

        (x,y,z,d) = self.parent().pol_ring().gens()
        (X,Y,Z,dX,dY,dZ) = self.parent().diff_alg().gens()
        L = op.monomials()
        new_rat = 0
        for mon in L:
            mon_summand  = self._rat
            mon_summand  = mon_summand.derivative(x,mon.degree(dX))
            mon_summand  = mon_summand.derivative(y,mon.degree(dY))
            mon_summand  = mon_summand.derivative(z,mon.degree(dZ))
            mon_summand *= x**(mon.degree(X))
            mon_summand *= y**(mon.degree(Y))
            mon_summand *= z**(mon.degree(Z))
            new_rat     += op.monomial_coefficient(mon)*mon_summand
        res = self.parent().rat_field()(new_rat)
        if (new_parent == None):
            new_parent = self.parent().extend_type(["quasi", "mero"], ring=True)
        return new_parent(res).reduce()

    # note that this is qd/dq, resp 1/(2*pi*i)*d/dtau
    def derivative(self):
        r"""
        Return the derivative ``d/dq = 1/(2*pi*i) d/dtau`` of ``self``.

        Note that the parent might (probably will) change.
        In particular its analytic type will be extended
        to contain "quasi".

        If ``parent.has_reduce_hom() == True`` then
        the result is reduced to be an element of
        the corresponding forms space if possible.
        
        In particular this is the case if ``self``
        is a (homogeneous) element of a forms space.
        """

        return self.diff_op(self.parent()._derivative_op, self.parent().extend_type("quasi", ring=True))

    def serre_derivative(self):
        r"""
        Return the Serre derivative of ``self``.

        Note that the parent might (probably will) change.
        However a modular element is returned if ``self``
        was already modular.

        If ``parent.has_reduce_hom() == True`` then
        the result is reduced to be an element of
        the corresponding forms space if possible.
        
        In particular this is the case if ``self``
        is a (homogeneous) element of a forms space.
        """
        return self.diff_op(self.parent()._serre_derivative_op, self.parent().extend_type(ring=True))

    @cached_method
    def order_inf(self):
        """
        Return the order at infinity of ``self``.

        If ``self`` is homogeneous and modular then
        only the rational function ``self.rat()`` is used.
        Otherwise the Fourier expansion is used
        (with increasing precision until the order
        can be determined).
        """

        if self.is_zero():
            return infinity

        if (self.is_homogeneous() and self.is_modular()):
            rat       = self.parent().rat_field()(self._rat)
            R         = self.parent().pol_ring()
            numerator = R(rat.numerator())
            denom     = R(rat.denominator())
            (x,y,z,d) = R.gens()
            # We intentially leave out the d-factor!
            finf_pol  = (x**self.hecke_n()-y**2)
    
            order_inf = 0
            # There seems to be a bug in Singular, for now this "try, except" is a workaround
            # Also numerator /= finf_pol doesn't seem to return an element of R for non-exact rings...
            try:
                while (finf_pol.divides(numerator)):
                    numerator  = numerator.quo_rem(finf_pol)[0]
                    #numerator /= finf_pol
                    numerator  = R(numerator)
                    order_inf += 1
            except TypeError:
                pass
            try:
                while (finf_pol.divides(denom)):
                    denom      = denom.quo_rem(finf_pol)[0]
                    #denom     /= finf_pol
                    denom      = R(denom)
                    order_inf -= 1
            except TypeError:
                pass

            return order_inf
        #elif False:
        #    n   = self.hecke_n()
        #    k   = self.weight()
        #    ep  = self.ep()
        #    dim = sum([\
        #              QQ( (k - 2*r)*(n - 2)/(4*n) - (1 - ep*(-1)**r)/4 ).floor()\
        #              + 1 for r in range(ZZ(0), QQ(k/ZZ(2)).floor() + 1) ])
        else:
            num_val   = prec_num_bound   = 1 #(self.parent()._prec/ZZ(2)).ceil()
            denom_val = prec_denom_bound = 1 #(self.parent()._prec/ZZ(2)).ceil()

            while (num_val >= prec_num_bound):
                prec_num_bound   *= 2
                num_val   = self.numerator().q_expansion(prec=prec_num_bound, fix_prec=True).valuation()
            while (denom_val >= prec_denom_bound):
                prec_denom_bound *= 2
                denom_val = self.denominator().q_expansion(prec=prec_denom_bound, fix_prec=True).valuation()

            return (num_val-denom_val)

    def as_ring_element(self):
        r"""
        Coerce ``self`` into the graded ring of its parent.
        """

        return self.parent().graded_ring()(self._rat)

    def reduce(self):
        r"""
        In case ``self.parent().has_reduce_hom() == True``
        and ``self`` is homogeneous. The converted element
        lying in the corresponding homogeneous_space is returned.
        
        Otherwise ``self`` is returned.
        """

        if self.parent().has_reduce_hom() and self.is_homogeneous():
            return self.parent().homogeneous_space(self._weight, self._ep)(self._rat)
        else:
            return self

    def force_reduce(self):
        r"""
        If ``self`` is homogeneous. The converted element
        lying in the corresponding homogeneous_space is returned.
        
        Otherwise ``self`` is returned.
        """

        if self.is_homogeneous():
            return self.parent().homogeneous_space(self._weight, self._ep)(self._rat)
        else:
            return self

    def reduced_parent(self):
        r"""
        Return the space with the analytic type of ``self``.
        If ``self`` is homogeneous the corresponding ``FormsSpace`` is returned.
        
        I.e. return the smallest known ambient space of ``self``.
        """

        if self.is_homogeneous():
            return FormsSpace(self.analytic_type(), self.group(), self.base_ring(), self.weight(), self.ep())
        else:
            return FormsRing(self.analytic_type(), self.group(), self.base_ring(), self.parent().has_reduce_hom())

    def full_reduce(self):
        r"""
        Convert ``self`` into its reduced parent.
        """

        return self.reduced_parent()(self._rat)

    #precision is actually acuracy, maybe add "real precision" meaning number of rel. coef
    @cached_method
    def q_expansion_cached(self, prec, fix_d, d_num_prec, fix_prec = False):
        """
        Returns the Fourier expansion of self (cached).

        INPUT:

        - ``prec``        - An integer, the desired output precision O(q^prec).

        - ``fix_d``       - ``False`` or a value to substitute for d.
                            The base_ring will be changed accordingly (if possible).
                            If ``True`` is used then the numerical value of d
                            corresponding to n will be used.
                            If n = 3, 4, 6 the used value is exact.
                            Also see ``MFSeriesConstructor``.

        - ``d_num_prec``  - An integer, namely the precision to be used if a
                            numerical value for d is substituted.

        - ``fix_prec``    - If ``fix_prec`` is not ``False`` (default)
                            then the precision of the ``MFSeriesConstructor`` is
                            set such that the output has exactly the specified
                            precision O(q^prec).

        OUTPUT:

        The Fourier expansion of self as a ``FormalPowerSeries`` or ``FormalLaurentSeries``.
        """

        if (fix_prec == False):
            #if (prec <1):
            #    print "Warning: non-positiv precision!"
            if not (fix_d or self.base_ring().is_exact()):
                print "Warning: For non-exact base rings it is strongly recommended to use fix_d!"
            if ((not self.is_zero()) and prec <= self.order_inf()):
                print "Warning: precision too low to determine any coefficient!"

            # This should exactly ensure the given precision O(q^prec)
            # The result will have "max(prec-self.order_inf(),0)" significant coefficients
            prec += max(-2*self.order_inf(),0)
            # The following line would instead give "prec" many significant coefficients:
            # prec += max(-2*self.order_inf(),0) + self.order_inf()
            # The following line would instead ensure that "at least" the given prec and sig. coeff
            # prec += max(-2*self.order_inf(),0) + max(self.order_inf() + sigcoeff - prec,0)

        #dhom  = self.rat_field().hom([SC.F_rho_ZZ(), SC.F_i_ZZ(), SC.E2_ZZ(), SC.d()],SC.coeff_ring())
        SC    = MFSeriesConstructor(self.group(), self.base_ring(), prec, fix_d, d_num_prec)
        X     = SC.F_rho()
        Y     = SC.F_i()
        D     = SC.d()
        q     = SC._qseries_ring.gen()
        if (self.parent().is_modular()):
            qexp = self._rat.subs(x=X,y=Y,d=D)
        else:
            Z = SC.E2()
            qexp = self._rat.subs(x=X,y=Y,z=Z,d=D)
        return (qexp + O(q**prec)).parent()(qexp)

    def q_expansion(self, prec = None, fix_d = False, d_num_prec = None, fix_prec = False):
        """
        Returns the Fourier expansion of self.

        INPUT:

        - ``prec``        - An integer, the desired output precision O(q^prec).
                            Default: ``None`` in which case the default precision
                            of ``self.parent()`` is used.

        - ``fix_d``       - ``False`` (default) or a value to substitute for d.
                            The base_ring will be changed accordingly (if possible).
                            If ``True`` is used then the numerical value of d
                            corresponding to n will be used.
                            If n = 3, 4, 6 the used value is exact.
                            Also see ``MFSeriesConstructor``.

        - ``d_num_prec``  - The precision to be used if a numerical value for d is substituted.
                            Default: ``None`` in which case the default
                            numerical precision of ``self.parent()`` is used.

        - ``fix_prec``    - If ``fix_prec`` is not ``False`` (default)
                            then the precision of the ``MFSeriesConstructor`` is
                            set such that the output has exactly the specified
                            precision O(q^prec).

        OUTPUT:

        The Fourier expansion of self as a ``FormalPowerSeries`` or ``FormalLaurentSeries``.
        """

        if prec == None:
            prec = self.parent()._prec
        if d_num_prec == None:
            d_num_prec = self.parent()._num_prec
        return self.q_expansion_cached(prec, fix_d, d_num_prec, fix_prec)

    def q_expansion_fixed_d(self, prec = None, d_num_prec = None, fix_prec = False):
        """
        Returns the Fourier expansion of self.
        The numerical (or exact) value for d is substituted.


        INPUT:

        - ``prec``        - An integer, the desired output precision O(q^prec).
                            Default: ``None`` in which case the default precision
                            of ``self.parent()`` is used.

        - ``d_num_prec``  - The precision to be used if a numerical value for d is substituted.
                            Default: ``None`` in which case the default
                            numerical precision of ``self.parent()`` is used.

        - ``fix_prec``    - If ``fix_prec`` is not ``False`` (default)
                            then the precision of the ``MFSeriesConstructor`` is
                            set such that the output has exactly the specified
                            precision O(q^prec).

        OUTPUT:

        The Fourier expansion of self as a ``FormalPowerSeries`` or ``FormalLaurentSeries``.
        """
        return self.q_expansion(prec, True, d_num_prec, fix_prec)

    def __call__(self, tau, prec = None, num_prec = None):
        r"""
        Try too return ``self`` evaluated at a point ``tau``
        in the upper half plane, where ``self`` is interpreted
        as a function in ``tau``, where ``q=exp(2*pi*i*tau)``.
        
        Note that this interpretation might not make sense
        (and fail) for certain (many) choices of
        (``base_ring``, ``tau.parent()``).

        To obtain a precise and fast result the parameters
        ``prec`` and ``num_prec`` both have to be considered/balanced.
        A high ``prec`` value is usually quite costly.

        INPUT:
        
        - ``tau``        - ``infinity`` or an element of the upper
                           half plane. E.g. with parent ``AA`` or ``CC``.

        - ``prec``       - An integer, namely the precision used for the
                           Fourier expansion. If ``prec == None`` (default)
                           then the default precision of ``self.parent()``
                           is used.
                      
        - ``num_prec``   - An integer, namely the minimal numerical precision
                           used for ``tau`` and ``d``. If `num_prec == None`
                           (default) then the default numerical precision of
                           ``self.parent()`` is used.

        OUTPUT:

        The (numerical) evaluated function value.


        ALGORITHM:

        #. If (tau == infinity):
           Return ``infinity`` unless the analytic type of
           ``self`` is at most ``holomorphic`` in which
           case the Fourier expansion (with precision ``1``)
           is evaluated at ``zero``.

        #. Else if ``self`` is homogeneous and modular:
        
           Determine the matrix ``A`` which sends ``tau``
           to ``w`` in the fundamental domain, together
           with ``aut_factor(A,w)``.
           
           Note: These values are determined by the method
           ``get_FD(tau, aut_factor)`` from ``self.group()``,
           where ``aut_factor = self.parent().aut_factor``
           (which is only defined on the basic generators).

           Because of the (modular) transformation property
           of ``self`` the evaluation at ``tau`` is given by
           the evaluation at ``w`` multiplied by ``aut_factor(A,w)``.

           The evaluation at ``w`` is calculated by
           evaluating the truncated Fourier expansion of
           self at ``q(w)``.
           
           Note that this is much faster and more precise
           than a direct evaluation at ``tau``.

        #. Else if ``self`` is exactly ``E2``:
           The same procedure as before is applied (with
           the aut_factor from the corresponding modular
           space). Except that at the end a correction
           term for the quasimodular form ``E2`` of the form 
           ``4*lambda/(2*pi*i)*n/(n-2) * c*(c*w + d)``
           has to be added, where ``lambda = 2*cos(pi/n)``
           and ``c,d`` are the lower entries of the matrix
           ``A``.

        #. Else:
           Evaluate ``F_rho, F_i, E2`` at ``tau``
           using the above procedures. Substitute
           ``x=F_rho(tau), y=F_i(tau), z=E2(tau)``
           and the numerical value of ``d`` for ``d``
           in ``self.rat()``.
        """

        if (prec == None):
            prec = self.parent().default_prec()
        if (num_prec == None):
            num_prec = self.parent().default_num_prec()
    
        if (tau==infinity):
            if (self.AT("cusp") >= self.analytic_type()):
                return ZZ(0)
            if (self.AT("holo") >= self.analytic_type()):
                return self.q_expansion(prec=1)[0]
            else:
                return infinity

        num_prec = max(\
            ZZ(getattr(tau,'prec',lambda: num_prec)()),\
            num_prec\
        )
        tau = tau.n(num_prec)
        (x,y,z,d) = self.parent().rat_field().gens()

        if (self.is_homogeneous() and self.is_modular()):
            q_exp = self.q_expansion_fixed_d(prec=prec, d_num_prec=num_prec)
            A, w, aut_factor = self.group().get_FD(tau,self.parent().aut_factor)
            if (type(q_exp) == LaurentSeries):
                return q_exp.laurent_polynomial()(exp((2*pi*i).n(num_prec)/self.group().lam*w))*aut_factor
            else:
                return q_exp.polynomial()(exp((2*pi*i).n(num_prec)/self.group().lam*w))*aut_factor
        elif (self._rat == z):
            E2 = self.parent().graded_ring().E2()
            A, w, aut_factor = self.group().get_FD(tau,E2.parent().aut_factor)
            E2_wvalue = E2.q_expansion_fixed_d(prec=prec, d_num_prec=num_prec).polynomial()(exp((2*pi*i).n(num_prec)/self.group().lam*w))
            E2_cor_term = 4*self.group().lam/(2*pi*i).n(num_prec)*self.hecke_n()/(self.hecke_n()-2) * A[1][0]*(A[1][0]*w + A[1][1])
            return E2_wvalue*aut_factor + E2_cor_term
        else:
            F_rho = self.parent().graded_ring().F_rho()
            F_i   = self.parent().graded_ring().F_i()
            E2    = self.parent().graded_ring().E2()
            dval  = self.parent().group().dvalue().n(num_prec)
            return self._rat.subs(x=F_rho(tau), y=F_i(tau), z=E2(tau), d=dval)
