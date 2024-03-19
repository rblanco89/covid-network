COMPILER = g++
LIBS = -lm
CC = $(COMPILER) 
OBJS = mainNetwork.o

simNetwork : $(OBJS)
	$(CC) $^ -o $@ $(LIBS)

%.o : %.cpp
	$(CC) -c $< -o $@

.PHONY: clean

clean:
	rm -f *.o *~
