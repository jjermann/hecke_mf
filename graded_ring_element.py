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
    from analytic_type import AnalyticType
    AT = AnalyticType()

    @staticmethod
    def __classcall__(cls, parent, rat):
        rat = parent.rat_field()(rat)
        # rat.reduce() <- maybe add this for the nonexact case

        return super(FormsRingElement,cls).__classcall__(cls, parent, rat)

    def __init__(self, parent, rat):
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
        """
        Return the group for which self is a (Hecke) meromorphic modular form.
        """
        return self.parent().group()
    def hecke_n(self):
        """
        Return the n corresponding to the group of self.
        """
        return self.parent().hecke_n()
    def base_ring(self):
        """
        Return the base ring of self.
        """
        return self.parent().base_ring()
    def coeff_ring(self):
        """
        Return the coefficient ring of self.
        """
        return self.parent().coeff_ring()
    def rat(self):
        """
        Return the rational function representing self.
        """
        return self._rat
    def is_homogeneous(self):
        return self._weight != None
    def weight(self):
        return self._weight
    def ep(self):
        return self._ep
    def degree(self):
        return (self._weight,self._ep)
    def is_modular(self):
        return not (self.AT("quasi") <= self._analytic_type)
    def is_weakly_holomorphic(self):
        return self.AT("weak", "quasi") >= self._analytic_type
    def is_holomorphic(self):
        return self.AT("holo", "quasi") >= self._analytic_type
    def is_cuspidal(self):
        return self.AT("cusp", "quasi") >= self._analytic_type
    def is_zero(self):
        return self.AT(["quasi"]) >= self._analytic_type
    def analytic_type(self):
        return self._analytic_type

    def numerator(self):
        res = self.parent().rat_field()(self._rat.numerator())
        # In general the numerator has a different weight than the original function...
        new_parent = self.parent().extend_type(ring=True).reduce_type(["holo", "quasi"])
        return new_parent(res)
    def denominator(self):
        res = self.parent().rat_field()(self._rat.denominator())
        # In general the denominator has a different weight than the original function...
        new_parent = self.parent().extend_type(ring=True).reduce_type(["holo", "quasi"])
        return new_parent(res)
    def _add_(self,other):
        return self.parent()(self._rat+other._rat)
    def _sub_(self,other):
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
        res = self.parent().rat_field()(self._rat*other._rat)
        new_parent = self.parent().extend_type(ring=True)
        # The product of two homogeneous elements is homogeneous
        return new_parent(res).reduce()
    def _div_(self,other):
        res = self.parent().rat_field()(self._rat/other._rat)
        new_parent = self.parent().extend_type("mero", ring=True)
        # The division of two homogeneous elements is homogeneous
        return new_parent(res).reduce()
    def sqrt(self):
        res = self.parent().rat_field()(self._rat.sqrt())
        new_parent = self.parent().extend_type(ring=True)
        # The sqrt of a homogeneous element is homogeneous if it exists
        return self.parent()(res).reduce()
    #def __invert__(self,other):
    #    res = self.parent().rat_field()(1/self._rat)
    #    new_parent = self.parent().extend_type(ring=True, mero=True)
    #    return new_parent(res).reduce()

    def diff_op(self, op, new_parent=None):
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
        return self.diff_op(self.parent()._derivative_op, self.parent().extend_type("quasi", ring=True))
    def serre_derivative(self):
        return self.diff_op(self.parent()._serre_derivative_op, self.parent().extend_type(ring=True))

    #TODO: this only works for modular objects
    @cached_method
    def order_inf(self):
        """
        Return the order at infinity of self.
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
        return self.parent().graded_ring()(self._rat)

    def reduce(self):
        if self.parent().has_reduce_hom() and self.is_homogeneous():
            return self.parent().homogeneous_space(self._weight, self._ep)(self._rat)
        else:
            return self

    def force_reduce(self):
        if self.is_homogeneous():
            return self.parent().homogeneous_space(self._weight, self._ep)(self._rat)
        else:
            return self

    def reduced_parent(self):
        if self.is_homogeneous():
            return FormsSpace(self.analytic_type(), self.group(), self.base_ring(), self.weight(), self.ep())
        else:
            return FormsRing(self.analytic_type(), self.group(), self.base_ring(), self.parent().has_reduce_hom())

    def full_reduce(self):
        return self.reduced_parent()(self._rat)

    #precision is actually acuracy, maybe add "real precision" meaning number of rel. coef
    @cached_method
    def q_expansion_cached(self, prec, fix_d, d_num_prec, fix_prec = False):
        """
        Returns the Fourier expansion of self.
        The output should have exactly the specified precision O(q^prec).

        INPUT:

        - ``prec``        - The desired output precision O(q^prec)
        - ``fix_d``       - ``False`` (default) or a value to substitute for d.
                            The base_ring will be changed accordingly (if possible).
                            If ``True`` is used then the numerical value of d
                            corresponding to n will be used.
                            If n = 3, 4, 6 the used value is exact.
        - ``d_num_prec``  - ``53`` (default), the precision to be used if a
                            numerical value for d is substituted.

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
        if prec == None:
            prec = self.parent()._prec
        if d_num_prec == None:
            d_num_prec = self.parent()._num_prec
        return self.q_expansion_cached(prec, fix_d, d_num_prec, fix_prec)

    def q_expansion_fixed_d(self, prec = None, d_num_prec = None, fix_prec = False):
        """
        Returns the Fourier expansion of ``self``.
        The numerical (or exact) value for d is substituted.
        The output should have exactly the specified precision O(q^prec).

        INPUT:

        - ``prec``        - The desired output precision O(q^prec)
        - ``d_num_prec``  - ``53`` (default), the precision to be used
                            for the substituted d value.

        OUTPUT:

        The Fourier expansion of self as a ``FormalPowerSeries`` or ``FormalLaurentSeries``.
        """
        return self.q_expansion(prec, True, d_num_prec, fix_prec)

    def __call__(self, tau, prec = ZZ(10), num_prec = ZZ(53)):
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
