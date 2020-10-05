test: $(patsubst src/test/test_%.m,test_%,$(wildcard src/test/*.m))
# test: test_Montgomery	test_OddIsogenies

test_%: src/test/test_%.m
	echo "\n\033[0;31m\033[1mTesting target: $@\033[0m"
	echo 'AttachSpec("src/spec"); load "$?";' | /usr/local/magma/./magma -b -S 12345

sqisign:
	/usr/local/magma/./magma src/sqisign.m
