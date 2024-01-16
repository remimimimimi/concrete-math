(TeX-add-style-hook
 "root"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "11pt" "a4paper")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("fontenc" "T1")))
   (TeX-run-style-hooks
    "latex2e"
    "session"
    "article"
    "art11"
    "fontenc"
    "isabelle"
    "isabellesym"
    "pdfsetup")
   (LaTeX-add-bibliographies))
 :latex)

