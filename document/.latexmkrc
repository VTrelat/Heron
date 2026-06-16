# .latexmkrc — latexmk configuration for this report.
#
#   latexmk        build report.pdf (into build/)
#   latexmk -pvc   build + watch for changes
#   latexmk -C     clean all generated files
#
# Run it locally (a TeX Live / MacTeX installation with latexmk on PATH).

$pdf_mode = 1;                  # produce a PDF via pdflatex
$out_dir  = 'build';            # keep auxiliary files and the PDF out of the source tree
@default_files = ('report.tex');
$clean_ext = 'synctex.gz run.xml bbl';
