all:
	echo "stsc3-som"

clean:
	rm -Rf dist dist-newstyle cabal.project.local *~
	(cd cmd ; make clean)
	find . -name '*.o' -exec rm {} +
	find . -name '*.hi' -exec rm {} +

push-all:
	r.gitlab-push.sh stsc3-som
	r.github-push.sh stsc3-som
