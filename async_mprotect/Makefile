KDIR=/lib/modules/`uname -r`/build

all: kbuild randwrite

kbuild:
	make -C $(KDIR) M=`pwd`

randwrite: randwrite.cpp
	g++ -Wall -g -O3 randwrite.cpp -o randwrite

clean:
	make -C $(KDIR) M=`pwd` clean
	rm -f *~ randwrite

