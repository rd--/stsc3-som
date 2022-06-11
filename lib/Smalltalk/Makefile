%.som : %.st
	stsc3 translate class --sort --tidy fileout som $< $@

%.class.st : %.som
	stsc3 translate class --sort som fileout $< $@

cat-all:
	stsc3 som cat *.som
