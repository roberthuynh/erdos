# Building the working manuscript

The source is `main.tex`; the readable artifact is `main.pdf`. Required dependencies: XeLaTeX or Tectonic with fontspec, unicode-math, Times New Roman, Arial, Courier New and Latin Modern Math. The fonts must be installed and discoverable by family name.

From this directory, compile with `tectonic main.tex`. A cached or offline build additionally requires the TeX packages and fonts to be cached. Compilation checks typesetting only. The package verification guide describes the separate accepted mathematical evidence.
