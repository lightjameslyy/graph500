.PHONY: clean all

CC = mpicc
#CFLAGS = -Drestrict=__restrict__ -O3 -w -DGRAPH_GENERATOR_MPI
CFLAGS = -Drestrict=__restrict__ -O3
INC = -I..
LDFLAGS = 
LDLIBS = 

EXESRCS = $(wildcard *.c)
SRCS = $(wildcard ../*.c)
#OBJS = $(patsubst %.c, %.o, $(SRCS))
OBJS = ../graph_generator.o ../make_graph.o ../splittable_mrg.o ../utils.o
TARGETS = $(patsubst %.c, %.bin, $(EXESRCS))

%.o: %.c 
	$(CC) $(CFLAGS) $(INC) -c $< -o $@

%.bin: %.c $(OBJS)
	$(CC) $(CFLAGS) $^ -o $@ $(LDFLAGS) $(LDLIBS)
	
all: $(TARGETS)

../splittable_mrg.o: ../splittable_mrg.c ../mrg_transitions.c
	$(CC) $(CFLAGS) $(INC) -c $< -o $@

clean:
	$(RM) $(TARGETS) $(OBJS)

