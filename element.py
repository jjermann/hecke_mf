r"""
Elements of Hecke modular forms spaces

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

from graded_ring_element import FormsRingElement


class FormsElement(FormsRingElement):
    """
    (Hecke) modular forms.
    """

    def __init__(self, parent, rat):
        r"""
        An element of a space of (Hecke) modular forms.

        INPUT:

        - ``parent``      - a modular form space
        - ``rat``         - a rational function which corresponds to a
                            modular form in the modular form space

        OUTPUT:

        A (Hecke) modular form element corresponding to the given rational function
        with the given parent space.
        """

        super(FormsElement, self).__init__(parent, rat)

        if self.AT(["quasi"])>=self._analytic_type:
            pass
        elif not (
            self.is_homogeneous() and\
            self._weight  == parent.weight() and\
            self._ep      == parent.ep() ):
                raise Exception("{} does not correspond to an element of {}.".format(rat, parent))

    def _repr_(self):
        """
        Return the string representation of self.
        """

        n=self.hecke_n()

        # For now the series constructor doesn't behave well for non exact bases... :(
        if (self.group().is_arithmetic() or not self.base_ring().is_exact()):
            return str(self.q_expansion_fixed_d().add_bigoh(self.parent()._disp_prec))
        else:
            return str(self.q_expansion().add_bigoh(self.parent()._disp_prec))

    def _latex_(self):
        r"""
        Return the LaTeX representation of ``self``.
        """

        return super(FormsElement, self)._latex_()

    def coordinate_vector(self):
        r"""
        Return the coordinate vector of ``self`` with
        respect to ``self.parent().gens()``.

        The returned coordinate vector is an element
        of ``self.parent().ambient_module()``.        
        
        This uses the the corresponding function of the
        parent. If the parent has not defined a coordinate
        vector function or an ambient module for coordinate
        vectors then an exception is raised by the parent
        (default implementation).
        """

        return self.parent().coordinate_vector(self)
        