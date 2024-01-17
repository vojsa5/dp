.PHONY: all
all: assembly

.PHONY: assembly
assembly:
	sbt test assembly

.PHONY: test
test:
	tests/test.sh

# once you have an interpreter ready, use the following line
#	tests/test.sh

.PHONY: docker
docker:
	sbt docker
	docker push fikovnik/microc

.PHONY: docker-build
docker-build:
	docker build -t fikovnik/microc-build -f project/microc-build-image/Dockerfile .
	docker push fikovnik/microc-build
