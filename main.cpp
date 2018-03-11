#include "Utility.h"
#include "Graph.h"

int main(int argc, char *argv[]) {
	if(argc < 4) {
		printf("Usage: [1]exe [2]graph-dir [3]epsilon [4]mu\n");
		return 0;
	}

#ifdef _DEBUG_
	printf("**** TriL-SCAN (Debug): %s %s %s *** ", argv[1], argv[2], argv[3]);
#else
	printf("**** TriL-SCAN (Release): %s %s %s *** ", argv[1], argv[2], argv[3]);
#endif

	printf("\n");

#ifdef _LINUX_
	struct timeval start, end1, end;
	gettimeofday(&start, NULL);
#else
	int start, end1, end;
	start = clock();
#endif

	Graph *graph = new Graph(argv[1]);
	graph->read_graph();
	//printf("\t*** Finished reading graph\n");

#ifdef _LINUX_
	gettimeofday(&end1, NULL);

	long long mtime1, seconds1, useconds1;
	seconds1 = end1.tv_sec - start.tv_sec;
	useconds1 = end1.tv_usec - start.tv_usec;
	mtime1 = seconds1*1000000 + useconds1;
#else
	end1 = clock();
#endif

	if(argc >= 5&&strcmp(argv[4], "output") == 0) graph->scan(argv[2], argv[3], 1);
	else graph->scan(argv[2], argv[3], 0);

#ifdef _LINUX_
	gettimeofday(&end, NULL);

	long long mtime, seconds, useconds;
	seconds = end.tv_sec - start.tv_sec;
	useconds = end.tv_usec - start.tv_usec;
	mtime = seconds*1000000 + useconds;

	printf("Total time excluding IO is: %lld\n", mtime-mtime1);
#else
	end = clock();

	printf("IO time: %d, Hash time: %d, Triangle time: %d, Total time(w/o IO): %d\n", end1-start, end2-end1, end-end2, end-end1);
#endif

	return 0;
}
