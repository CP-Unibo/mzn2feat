XFLAGS=   `xml2-config --cflags`
GFLAGS= 
XLIBS=    `xml2-config --libs`
GLIBS=    
CXXFLAGS= -g -Wall -ansi -pedantic $(XFLAGS) $(GFLAGS) -I.
LDFLAGS=  $(GLIBS) $(XLIBS)

all: xcsp2mzn

xcsp2mzn: xcsp2mzn.o
	g++   -o $@ $^ $(LDFLAGS)
	cp xcsp2mzn ../bin
%.o: %.cpp xcsp-parser/*.h xcsp-parser/*.hh Makefile
	g++ $(CXXFLAGS) -c -o $@ $<
	
clean:
	rm -rf *o xcsp2mzn
