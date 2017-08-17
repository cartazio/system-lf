# how to generate HIW slides

see the file ./latex/hiw2017slides.tex

you will need a recent texlive installed,
plus pygments installed so you can use the minted syntax highlighting package

i personally use latexmk + sublime text 3 + skim for generating this document,

my latexmk config at `~/.latexmkrc` is

```

# this is perl code, thats also the latexmk pref file
$pdf_mode = 1 ;
$pdf_previewer  = "open  -a skim   %S --args %O";
$pdf_update_method= 0; #  do nothing
$pdflatex ="pdflatex   -interaction=nonstopmode --shell-escape --synctex=1 %O %S";
$view = "pdf";
```

run latexmk in the `./latex` dir and it should just do the right thing
with the following command `latexmk -pvc`
