.PHONY: clean CheatSheet.pdf

CheatSheet.pdf:
	latexmk -lualatex -shell-escape CheatSheet

clean:
	@rm -f *.dvi *.aux *.fls *.ps *.log *.fdb_latexmk *~ *.out *.blg *.bbl *.synctex.gz *.bak *.xmpi *.xmpdata
	@rm -rf _minted-*
	@ls *.pdf | grep -v '^CheatSheet' | xargs rm

pip:
	pip install pygments-mathematica
