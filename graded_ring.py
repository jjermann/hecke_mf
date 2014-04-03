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

from sage.rings.all import ZZ, QQ, infinity

from sage.rings.ring import CommutativeAlgebra
from sage.categories.all import CommutativeAlgebras
from sage.structure.unique_representation import UniqueRepresentation
from sage.misc.cachefunc import cached_method

from hecke_triangle_groups import HeckeTriangleGroup
from abstract_ring import FormsRing_abstract


def canonical_parameters(group, base_ring, red_hom):
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

    red_hom = bool(red_hom)

    return (group, base_ring, red_hom)


class QMModularFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    r"""
    Graded ring of (Hecke) quasi meromorphic modular forms
    for the given group and base ring
    """

    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        r"""
        Return a (cached) instance with canonical parameters.
        """

        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)

    def __init__(self, group, base_ring, red_hom):
        r"""
        Return the graded ring of (Hecke) quasi meromorphic modular forms
        for the given ``group`` and ``base_ring``.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``base_ring``   - The base_ring (default: ``ZZ``).
        - ``red_hom``     - If True then results of binary operations are considered
                            homogeneous whenever it makes sense (default: False).
                            This is mainly used by the homogeneous spaces.

        OUTPUT:

        The corresponding graded ring of (Hecke) quasi meromorphic modular forms
        for the given ``group`` and ``base_ring``.
        """

        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["quasi", "mero"])

class QWeakModularFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    r"""
    Graded ring of (Hecke) quasi weakly holomorphic modular forms
    for the given group and base ring
    """

    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        r"""
        Return a (cached) instance with canonical parameters.
        """

        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)

    def __init__(self, group, base_ring, red_hom):
        r"""
        Return the graded ring of (Hecke) quasi weakly holomorphic modular forms
        for the given ``group`` and ``base_ring``.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``base_ring``   - The base_ring (default: ``ZZ``).
        - ``red_hom``     - If True then results of binary operations are considered
                            homogeneous whenever it makes sense (default: False).
                            This is mainly used by the homogeneous spaces.

        OUTPUT:

        The corresponding graded ring of (Hecke) quasi weakly holomorphic modular forms
        for the given ``group`` and ``base_ring``.
        """

        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["quasi", "weak"])

class QModularFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    r"""
    Graded ring of (Hecke) quasi modular forms
    for the given group and base ring
    """

    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        r"""
        Return a (cached) instance with canonical parameters.
        """

        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)

    def __init__(self, group, base_ring, red_hom):
        r"""
        Return the graded ring of (Hecke) quasi modular forms
        for the given ``group`` and ``base_ring``.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``base_ring``   - The base_ring (default: ``ZZ``).
        - ``red_hom``     - If True then results of binary operations are considered
                            homogeneous whenever it makes sense (default: False).
                            This is mainly used by the homogeneous spaces.

        OUTPUT:

        The corresponding graded ring of (Hecke) quasi modular forms
        for the given ``group`` and ``base_ring``.
        """

        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["quasi", "holo"])

class QCuspFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    r"""
    Graded ring of (Hecke) quasi cusp forms
    for the given group and base ring
    """

    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        r"""
        Return a (cached) instance with canonical parameters.
        """

        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)
    def __init__(self, group, base_ring, red_hom):
        r"""
        Return the graded ring of (Hecke) quasi cusp forms
        for the given ``group`` and ``base_ring``.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``base_ring``   - The base_ring (default: ``ZZ``).
        - ``red_hom``     - If True then results of binary operations are considered
                            homogeneous whenever it makes sense (default: False).
                            This is mainly used by the homogeneous spaces.

        OUTPUT:

        The corresponding graded ring of (Hecke) quasi cusp forms
        for the given ``group`` and ``base_ring``.
        """

        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["quasi", "cusp"])

class MModularFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    r"""
    Graded ring of (Hecke) meromorphic modular forms
    for the given group and base ring
    """

    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        r"""
        Return a (cached) instance with canonical parameters.
        """

        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)

    def __init__(self, group, base_ring, red_hom):
        r"""
        Return the graded ring of (Hecke) meromorphic modular forms
        for the given ``group`` and ``base_ring``.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``base_ring``   - The base_ring (default: ``ZZ``).
        - ``red_hom``     - If True then results of binary operations are considered
                            homogeneous whenever it makes sense (default: False).
                            This is mainly used by the homogeneous spaces.

        OUTPUT:

        The corresponding graded ring of (Hecke) meromorphic modular forms
        for the given ``group`` and ``base_ring``.
        """

        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["mero"])

class WeakModularFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    r"""
    Graded ring of (Hecke) weakly holomorphic modular forms
    for the given group and base ring
    """

    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        r"""
        Return a (cached) instance with canonical parameters.
        """

        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)
    def __init__(self, group, base_ring, red_hom):
        r"""
        Return the graded ring of (Hecke) weakly holomorphic modular forms
        for the given ``group`` and ``base_ring``.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``base_ring``   - The base_ring (default: ``ZZ``).
        - ``red_hom``     - If True then results of binary operations are considered
                            homogeneous whenever it makes sense (default: False).
                            This is mainly used by the homogeneous spaces.

        OUTPUT:

        The corresponding graded ring of (Hecke) weakly holomorphic modular forms
        for the given ``group`` and ``base_ring``.
        """

        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["weak"])

class ModularFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    r"""
    Graded ring of (Hecke) modular forms
    for the given group and base ring
    """

    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        r"""
        Return a (cached) instance with canonical parameters.
        """

        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)

    def __init__(self, group, base_ring, red_hom):
        r"""
        Return the graded ring of (Hecke) modular forms
        for the given ``group`` and ``base_ring``.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``base_ring``   - The base_ring (default: ``ZZ``).
        - ``red_hom``     - If True then results of binary operations are considered
                            homogeneous whenever it makes sense (default: False).
                            This is mainly used by the homogeneous spaces.

        OUTPUT:

        The corresponding graded ring of (Hecke) modular forms
        for the given ``group`` and ``base_ring``.
        """

        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["holo"])

class CuspFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    r"""
    Graded ring of (Hecke) cusp forms
    for the given group and base ring
    """

    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        r"""
        Return a (cached) instance with canonical parameters.
        """

        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)

    def __init__(self, group, base_ring, red_hom):
        r"""
        Return the graded ring of (Hecke) cusp forms
        for the given ``group`` and ``base_ring``.

        INPUT:

        - ``group``       - The Hecke triangle group (default: ``HeckeTriangleGroup(3)``)
        - ``base_ring``   - The base_ring (default: ``ZZ``).
        - ``red_hom``     - If True then results of binary operations are considered
                            homogeneous whenever it makes sense (default: False).
                            This is mainly used by the homogeneous spaces.

        OUTPUT:

        The corresponding graded ring of (Hecke) cusp forms
        for the given ``group`` and ``base_ring``.
        """

        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["cusp"])

