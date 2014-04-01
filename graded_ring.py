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
    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)
    def __init__(self, group, base_ring, red_hom):
        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["quasi", "mero"])

class QWeakModularFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)
    def __init__(self, group, base_ring, red_hom):
        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["quasi", "weak"])

class QModularFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)
    def __init__(self, group, base_ring, red_hom):
        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["quasi", "holo"])

class QCuspFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)
    def __init__(self, group, base_ring, red_hom):
        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["quasi", "cusp"])

class MModularFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)
    def __init__(self, group, base_ring, red_hom):
        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["mero"])

class WeakModularFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)
    def __init__(self, group, base_ring, red_hom):
        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["weak"])

class ModularFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)
    def __init__(self, group, base_ring, red_hom):
        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["holo"])

class CuspFormsRing(FormsRing_abstract, CommutativeAlgebra, UniqueRepresentation):
    @staticmethod
    def __classcall__(cls, group = HeckeTriangleGroup(3), base_ring = ZZ, red_hom = False):
        (group, base_ring, red_hom) = canonical_parameters(group, base_ring, red_hom)
        return super(FormsRing_abstract,cls).__classcall__(cls, group=group, base_ring=base_ring, red_hom=red_hom)
    def __init__(self, group, base_ring, red_hom):
        FormsRing_abstract.__init__(self, group=group, base_ring=base_ring, red_hom=red_hom)
        CommutativeAlgebra.__init__(self, base_ring=self.coeff_ring(), category=CommutativeAlgebras(self.coeff_ring()))
        self._analytic_type = self.AT(["cusp"])
