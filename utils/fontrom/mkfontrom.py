#!/usr/bin/env python

# Copyright Jamie Iles, 2017
# Copyright Waldo Alvarez, 2023
# https://pipflow.com
#
# This file is part of s80x86.
#
# s80x86 is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# s80x86 is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with s80x86.  If not, see <http://www.gnu.org/licenses/>.

import sys

with open("cp437-8x8", 'rb') as font:
    font_data = font.read()

with open("font.bin", 'w') as outfile:
    for c in font_data:
        for i in range(7,-1,-1):
            outfile.write('1\n' if (c & (1 << i)) else '0\n')
