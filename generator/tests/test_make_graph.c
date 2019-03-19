#include "../make_graph.h"
#include <time.h>

int main(int argc, char* argv[]) {
    printf("test make graph ... \n");
    int64_t nedges, i;
    packed_edge* result;
    make_graph(atoi(argv[1]), atoi(argv[2]), time(NULL), time(NULL)+1000, &nedges, &result);
    printf("nedges: %d\n", nedges);
    for (i = 0; i < nedges; i++) {
        printf("%d:%d:%d\n", i, get_v0_from_edge(result+i), get_v1_from_edge(result+i));
    }
    return 0;
}
