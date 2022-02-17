all:
	echo "stsc3-som"

clean:
	rm -Rf dist dist-newstyle *~
	(cd cmd ; make clean)
	find . -name '*.o' -exec rm {} +
	find . -name '*.hi' -exec rm {} +

push-all:
	r.gitlab-push.sh stsc3-som
