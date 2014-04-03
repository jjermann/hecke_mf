r"""
Modular forms for Hecke triangle groups

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

from sage.rings.all import ZZ, QQ, infinity

from sage.modules.module import Module
from sage.categories.all import Modules
from sage.modules.free_module import FreeModule
from sage.modules.free_module_element import vector
from sage.structure.unique_representation import UniqueRepresentation
from sage.misc.cachefunc import cached_method

from hecke_triangle_groups import HeckeTriangleGroup
from abstract_space import FormsSpace_abstract


def canonical_parameters(group, base_ring, k, ep):
    r"""
    Return a canonical version of the parameters.
    """

    if (group == infinity):
        group = HeckeTriangleGroup(infinity)
    else:
        try: 
            group = HeckeTriangleGroup(ZZ(group))
        except TypeError:
            group = HeckeTriangleGroup(group.n)

    n = group.n
    k = QQ(k)
    if (ep == None):   
        ep = (-1)**(k*ZZ(n-2)/ZZ(2))
    ep = ZZ(ep)
    num = (k-(1-ep)*n/(n-2))*(n-2)/4
    try:
        num = ZZ(num)
    except TypeError:
        raise Exception("Invalid resp. non-occuring weight!")

    return (group, base_ring, k, ep)


class QMModularForms(FormsSpace_abstract, Module, UniqueRepresentation):
    r"""
    Module of (Hecke) quasi meromorphic modular forms
    for the given group, base ring, weight and multiplier
    """
            
    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, k=QQ(0), ep=None):
        r"""
        Return a (cached) instance with canonical parameters.
        """

        (group, base_ring, k, ep) = canonical_parameters(group, base_ring, k, ep)
        return super(FormsSpace_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, k=k, ep=ep)

    def __init__(self, group, base_ring, k, ep):
        r"""
        Return the Module of (Hecke) quasi meromorphic modular forms
        of weight ``k`` with multiplier ``ep`` for the given ``group`` and ``base_ring``.
        """

        FormsSpace_abstract.__init__(self, group=group, base_ring=base_ring, k=k, ep=ep)
        Module.__init__(self, base=self.coeff_ring())
        self._analytic_type=self.AT(["quasi", "mero"])

# TODO: a quasi weak form here means that the denominator is at most a power of delta
class QWeakModularForms(FormsSpace_abstract, Module, UniqueRepresentation):
    r"""
    Module of (Hecke) quasi weakly holomorphic modular forms
    for the given group, base ring, weight and multiplier
    """
            
    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, k=QQ(0), ep=None):
        r"""
        Return a (cached) instance with canonical parameters.
        """

        (group, base_ring, k, ep) = canonical_parameters(group, base_ring, k, ep)
        return super(FormsSpace_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, k=k, ep=ep)

    def __init__(self, group, base_ring, k, ep):
        r"""
        Return the Module of (Hecke) quasi weakly holomorphic modular forms
        of weight ``k`` with multiplier ``ep`` for the given ``group`` and ``base_ring``.
        """

        FormsSpace_abstract.__init__(self, group=group, base_ring=base_ring, k=k, ep=ep)
        Module.__init__(self, base=self.coeff_ring())
        self._analytic_type=self.AT(["quasi", "weak"])

# TODO: a quasi modular form here means that it is a polynomial in F_rho, F_i, E2
class QModularForms(FormsSpace_abstract, Module, UniqueRepresentation):
    r"""
    Module of (Hecke) quasi modular forms
    for the given group, base ring, weight and multiplier
    """
            
    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, k=QQ(0), ep=None):
        r"""
        Return a (cached) instance with canonical parameters.
        """

        (group, base_ring, k, ep) = canonical_parameters(group, base_ring, k, ep)
        return super(FormsSpace_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, k=k, ep=ep)

    def __init__(self, group, base_ring, k, ep):
        r"""
        Return the Module of (Hecke) quasi modular forms
        of weight ``k`` with multiplier ``ep`` for the given ``group`` and ``base_ring``.
        """

        FormsSpace_abstract.__init__(self, group=group, base_ring=base_ring, k=k, ep=ep)
        Module.__init__(self, base=self.coeff_ring())
        self._analytic_type=self.AT(["quasi", "holo"])
        #self._ambient_module = FreeModule(self.coeff_ring(), self.dimension())

    def quasi_part_gens(self, r=0):
        r"""
        Return a basis of ``self`` for the submodule
        of quasi modular forms of the form ``E2^r*f``,
        where ``f`` is a modular form.
        """

        r = ZZ(r)
        if (r < 0 or 2*r > self._weight):
            return []

        gens = self.graded_ring().reduce_type("holo", degree=(self._weight-QQ(2*r), self._ep*(-1)**r)).gens()
        if (len(gens)>0):
            (x,y,z,d) = self.rat_field().gens()
            #gens = [ self.graded_ring().E2()**r*gen for gen in gens ]
            return [ self(z**r*gen._rat) for gen in gens ]
        else:
            return []

    @cached_method
    def gens(self):
        r"""
        Return a basis of ``self`` as a list of basis elements.
        """

        gens = []
        for r in range(ZZ(0), QQ(self._weight/ZZ(2)).floor()+1):
            gens.extend(self.quasi_part_gens(r))

        return gens

    @cached_method
    def dimension(self):
        r"""
        Return the dimension of ``self``.
        """
        n  = self.hecke_n()
        k  = self.weight()
        ep = self.ep()
        return sum([ 
            max( QQ( (k - 2*r)*(n - 2)/(4*n) - (1 - ep*(-1)**r)/4 ).floor() + 1, 0)\
            for r in range(ZZ(0), QQ(k/ZZ(2)).floor() + 1) ])

    # TODO: it is possible to define coordinate_vector!
    # for this a routine needs to be written to additively decompose
    # the polynomial according to the degree of z
    # the basis vector with respect to the above basis is then given
    # by concatenating the coordinate vectors for each (decomposed) part
    # However the above gens() has no nice relation to the Fourier coefficients
    # and it is expected to be hard(er) to write an algorithm to determine
    # the form by its fourier coefficients

# TODO: a cusp form here means that delta divides it...
class QCuspForms(FormsSpace_abstract, Module, UniqueRepresentation):
    r"""
    Module of (Hecke) quasi cusp forms
    for the given group, base ring, weight and multiplier
    """
            
    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, k=QQ(0), ep=None):
        r"""
        Return a (cached) instance with canonical parameters.
        """

        (group, base_ring, k, ep) = canonical_parameters(group, base_ring, k, ep)
        return super(FormsSpace_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, k=k, ep=ep)

    def __init__(self, group, base_ring, k, ep):
        r"""
        Return the Module of (Hecke) quasi cusp forms
        of weight ``k`` with multiplier ``ep`` for the given ``group`` and ``base_ring``.
        """

        FormsSpace_abstract.__init__(self, group=group, base_ring=base_ring, k=k, ep=ep)
        Module.__init__(self, base=self.coeff_ring())
        self._analytic_type=self.AT(["quasi", "cusp"])
        #self._ambient_module = FreeModule(self.coeff_ring(), self.dimension())

    def quasi_part_gens(self, r=0):
        r"""
        Return a basis of ``self`` for the submodule
        of quasi cusp forms of the form ``E2^r*f``,
        where ``f`` is a cusp form.
        """

        r = ZZ(r)
        if (r < 0 or 2*r > self._weight):
            return []

        gens = self.graded_ring().reduce_type("cusp", degree=(self._weight-QQ(2*r), self._ep*(-1)**r)).gens()
        if (len(gens)>0):
            (x,y,z,d) = self.rat_field().gens()
            #gens = [ self.graded_ring().E2()**r*gen for gen in gens ]
            return [ self(z**r*gen._rat) for gen in gens ]
        else:
            return []

    @cached_method
    def gens(self):
        r"""
        Return a basis of ``self`` as a list of basis elements.
        """

        gens = []
        for r in range(ZZ(0), QQ(self._weight/ZZ(2)).floor()+1):
            gens.extend(self.quasi_part_gens(r))

        return gens

    @cached_method
    def dimension(self):
        r"""
        Return the dimension of ``self``.
        """

        n  = self.hecke_n()
        k  = self.weight()
        ep = self.ep()
        return sum([ 
            max( QQ( (k - 2*r)*(n - 2)/(4*n) - (1 - ep*(-1)**r)/4 ).floor() + 0, 0)\
            for r in range(ZZ(0), QQ(k/ZZ(2)).floor() + 1) ])

    # TODO: it is possible to define coordinate_vector! (see above)

class MModularForms(FormsSpace_abstract, Module, UniqueRepresentation):
    r"""
    Module of (Hecke) meromorphic modular forms
    for the given group, base ring, weight and multiplier
    """
            
    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, k=QQ(0), ep=None):
        r"""
        Return a (cached) instance with canonical parameters.
        """

        (group, base_ring, k, ep) = canonical_parameters(group, base_ring, k, ep)
        return super(FormsSpace_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, k=k, ep=ep)

    def __init__(self, group, base_ring, k, ep):
        r"""
        Return the Module of (Hecke) meromorphic modular forms
        of weight ``k`` with multiplier ``ep`` for the given ``group`` and ``base_ring``.
        """

        FormsSpace_abstract.__init__(self, group=group, base_ring=base_ring, k=k, ep=ep)
        Module.__init__(self, base=self.coeff_ring())
        self._analytic_type=self.AT(["mero"])

class WeakModularForms(FormsSpace_abstract, Module, UniqueRepresentation):
    r"""
    Module of (Hecke) weakly holomorphic modular forms
    for the given group, base ring, weight and multiplier
    """
            
    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, k=QQ(0), ep=None):
        r"""
        Return a (cached) instance with canonical parameters.
        """

        (group, base_ring, k, ep) = canonical_parameters(group, base_ring, k, ep)
        return super(FormsSpace_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, k=k, ep=ep)

    def __init__(self, group, base_ring, k, ep):
        r"""
        Return the Module of (Hecke) weakly holomorphic modular forms
        of weight ``k`` with multiplier ``ep`` for the given ``group`` and ``base_ring``.
        """

        FormsSpace_abstract.__init__(self, group=group, base_ring=base_ring, k=k, ep=ep)
        Module.__init__(self, base=self.coeff_ring())
        self._analytic_type=self.AT(["weak"])

class ModularForms(FormsSpace_abstract, Module, UniqueRepresentation):
    r"""
    Module of (Hecke) modular forms
    for the given group, base ring, weight and multiplier
    """
            
    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, k=QQ(0), ep=None):
        r"""
        Return a (cached) instance with canonical parameters.
        """

        (group, base_ring, k, ep) = canonical_parameters(group, base_ring, k, ep)
        return super(FormsSpace_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, k=k, ep=ep)

    def __init__(self, group, base_ring, k, ep):
        r"""
        Return the Module of (Hecke) modular forms
        of weight ``k`` with multiplier ``ep`` for the given ``group`` and ``base_ring``.
        """

        FormsSpace_abstract.__init__(self, group=group, base_ring=base_ring, k=k, ep=ep)
        Module.__init__(self, base=self.coeff_ring())
        self._analytic_type = self.AT(["holo"])
        self._ambient_module = FreeModule(self.coeff_ring(), self.dimension())

    @cached_method
    def gens(self):
        r"""
        Return a basis of ``self`` as a list of basis elements.
        """

        return [ self.F_basis(m) for m in range(ZZ(0), -(self._l1 + 1), -1)]

    @cached_method
    def dimension(self):
        r"""
        Return the dimension of ``self``.
        """

        return max(self._l1+1, ZZ(0))

    def coordinate_vector(self, v):
        r"""
        Return the coordinate vector of ``v`` with respect to
        the basis ``self.gens()``.
        
        INPUT:

        - ``v``    - An element of ``self``.

        OUTPUT:

        An element of ``self.ambient_module()``, namely the
        corresponding coordinate vector of ``v`` with respect
        to the basis ``self.gens()``.

        The ambient module is the free module over the coefficient
        ring of ``self`` with the dimension of ``self``.
        """

        vec = v.q_expansion(prec=self.dimension()).padded_list()
        vec.pop(0)
        return self._ambient_module(vector(self.coeff_ring(), vec))

class CuspForms(FormsSpace_abstract, Module, UniqueRepresentation):
    r"""
    Module of (Hecke) cusp forms
    for the given group, base ring, weight and multiplier
    """
            
    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, k=QQ(0), ep=None):
        r"""
        Return a (cached) instance with canonical parameters.
        """

        (group, base_ring, k, ep) = canonical_parameters(group, base_ring, k, ep)
        return super(FormsSpace_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, k=k, ep=ep)

    def __init__(self, group, base_ring, k, ep):
        r"""
        Return the Module of (Hecke) cusp forms
        of weight ``k`` with multiplier ``ep`` for the given ``group`` and ``base_ring``.
        """

        FormsSpace_abstract.__init__(self, group=group, base_ring=base_ring, k=k, ep=ep)
        Module.__init__(self, base=self.coeff_ring())
        self._analytic_type=self.AT(["cusp"])
        self._ambient_module = FreeModule(self.coeff_ring(), self.dimension())

    @cached_method
    def gens(self):
        r"""
        Return a basis of ``self`` as a list of basis elements.
        """

        return [ self.F_basis(m) for m in range(ZZ(-1), -(self._l1 + 1), -1)]

    @cached_method
    def dimension(self):
        r"""
        Return the dimension of ``self``.
        """

        return max(self._l1, ZZ(0))

    def coordinate_vector(self, v):
        r"""
        Return the coordinate vector of ``v`` with respect to
        the basis ``self.gens()``.
        
        INPUT:

        - ``v``    - An element of ``self``.

        OUTPUT:

        An element of ``self.ambient_module()``, namely the
        corresponding coordinate vector of ``v`` with respect
        to the basis ``self.gens()``.

        The ambient module is the free module over the coefficient
        ring of ``self`` with the dimension of ``self``.
        """

        vec = v.q_expansion(prec=self.dimension()+1).padded_list()
        vec.pop(0)
        return self._ambient_module(vector(self.coeff_ring(), vec))

class ZeroForm(FormsSpace_abstract, Module, UniqueRepresentation):
    r"""
    Zero Module for the zero form for the given group, base ring
    weight and multiplier
    """
            
    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, k=QQ(0), ep=None):
        r"""
        Return a (cached) instance with canonical parameters.
        """

        (group, base_ring, k, ep) = canonical_parameters(group, base_ring, k, ep)
        return super(FormsSpace_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, k=k, ep=ep)

    def __init__(self, group, base_ring, k, ep):
        r"""
        Return the zero Module for the zero form of weight ``k`` with multiplier ``ep``
        for the given ``group`` and ``base_ring``.

        The ZeroForm space coerces into any forms space or ring with a compatible group.
        """

        FormsSpace_abstract.__init__(self, group=group, base_ring=base_ring, k=k, ep=ep)
        Module.__init__(self, base=self.coeff_ring())
        self._analytic_type=self.AT([])
        self._ambient_module = FreeModule(self.coeff_ring(), self.dimension())

    def _change_degree(self, k, ep):
        r"""
        Return the Zeroform space with a different weight ``k`` and multiplier ``ep``
        for the same group and base_ring.

        All those spaces coerce into each other.
        """
        return ZeroForm(group=self.group(), base_ring=self.base_ring(), k=k, ep=ep)

    @cached_method
    def gens(self):
        r"""
        Return a basis of ``self`` as a list of basis elements.
        Since this is the zero module an empty list is returned.
        """

        return []

    @cached_method
    def dimension(self):
        r"""
        Return the dimension of ``self``.
        Since this is the zero module ``0`` is returned.
        """

        return 0

    def coordinate_vector(self, v):
        r"""
        Return the coordinate vector of ``v`` with respect to
        the basis ``self.gens()``.

        Since this is the zero module which only contains
        the zero form the trivial vector in the trivial
        ambient module of dimension ``0`` is returned.
        """

        vec = []
        return self._ambient_module(vector(self.coeff_ring(), vec))
