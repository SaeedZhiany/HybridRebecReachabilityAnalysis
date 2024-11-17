package utils;

import com.fasterxml.jackson.annotation.JsonBackReference;
import com.fasterxml.jackson.annotation.JsonManagedReference;
import com.fasterxml.jackson.core.JsonProcessingException;
//import com.fasterxml.jackson.core.;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.ObjectWriter;
import org.apache.commons.lang3.tuple.Pair;
import stateSpace.HybridState;

import java.util.*;


public class ReachabilityAnalysisGraph {

    // HashMap to store the nodes by their IDs
    private Map<String, TreeNode> nodeMap;
    private Map<Integer, HybridState> intToNodeMap;
    private Map<HybridState, Integer> nodeToIntMap;
    private Integer counter;
    private ArrayList<Triple<Integer, Integer, String>> edges;

    // Root node of the graph
    private TreeNode root;

    public ReachabilityAnalysisGraph(HybridState rootData) {
        this.root = new TreeNode(rootData.getHash(), rootData);
        this.nodeMap = new HashMap<>();
        this.intToNodeMap = new HashMap<>();
        this.nodeToIntMap = new HashMap<>();
        this.edges = new ArrayList<>();
        this.nodeMap.put(root.getId(), root); // Add root to the map
        this.counter = 0;
        this.intToNodeMap.put(this.counter, rootData);
        this.nodeToIntMap.put(rootData, this.counter);
        this.counter++;
    }

    // Method to find a node in the graph by its ID
    public TreeNode findNodeInGraph(HybridState hybridState) {
        return nodeMap.get(hybridState.getHash());
    }

    // TreeNode class with parent-child relationships
    public static class TreeNode {
        private String id;
        private HybridState data;

        @JsonManagedReference // Manage serialization for the parent-child relationship
        private List<TreeNode> children;

        @JsonBackReference // Avoid recursion by not serializing parent in the child object
        private TreeNode parent;

        public TreeNode(String id, HybridState data) {
            this.id = id;
            this.data = data;
            this.children = new ArrayList<>();
        }

        // Add a child node and set its parent
        public void addChild(TreeNode child) {
            this.children.add(child);
            child.setParent(this);
        }

        public String getId() {
            return id;
        }

        public HybridState getData() {
            return data;
        }

        public List<TreeNode> getChildren() {
            return children;
        }

        public TreeNode getParent() {
            return parent;
        }

        public void setParent(TreeNode parent) {
            this.parent = parent;
        }
    }

    public TreeNode getRoot() {
        return root;
    }

    // Add a node to the graph and map
    public void addNode(TreeNode parent, HybridState nodeData, String message) {
        TreeNode newNode = new TreeNode(nodeData.getHash(), nodeData);
        parent.addChild(newNode);
        nodeMap.put(nodeData.getHash(), newNode); // Add the new node to the map
        intToNodeMap.put(this.counter, nodeData);
        nodeToIntMap.put(nodeData, this.counter);
        Integer parentIndex = this.nodeToIntMap.get(parent.getData()), childIndex = this.nodeToIntMap.get(nodeData);
        this.edges.add(new Triple<>(parentIndex, childIndex, message));
        this.counter++;
    }

    // Convert the root node and its children to JSON
    public String toJson() {
        ObjectMapper mapper = new ObjectMapper();

        // Increase the maximum nesting depth
//        StreamWriteConstraints constraints = StreamWriteConstraints.builder().maxNestingDepth(Integer.MAX_VALUE).build();
//        mapper.getFactory().setStreamWriteConstraints(constraints);

        ObjectWriter ow = mapper.writer().withDefaultPrettyPrinter();
        try {
            return ow.writeValueAsString(root);
        } catch (JsonProcessingException e) {
            throw new RuntimeException("Error converting tree to JSON", e);
        }
    }

    public String toDot() {
        String buffer = "";
        buffer += "digraph g {\n" +
                  "  edge [lblstyle=\"above, sloped\"];";

        Map<Integer, HybridState> sortedIntToNodeMap = new TreeMap<>(intToNodeMap);
        String templateIntToNodeMap = "  s%s [shape=\"square\" label=\"%s\"];\n";
        for (Map.Entry<Integer, HybridState> entry : sortedIntToNodeMap.entrySet()) {
            buffer += String.format(templateIntToNodeMap, entry.getKey(), entry.getKey());
        }

        String blackTemplateEdges = "  s%s -> s%s [label=\"%s\"];\n";
        String redTemplateEdges = "  s%s -> s%s [label=\"%s\", color=\"red\"];\n";

        for (Triple<Integer, Integer, String> entry : edges) {
            if (entry.value3.equals("PhysicalUpdate")) {
                buffer += String.format(blackTemplateEdges, entry.value1, entry.value2, entry.value3);
            } else {
                buffer += String.format(redTemplateEdges, entry.value1, entry.value2, entry.value3);
            }
        }

        buffer += "  __start0 [label=\"\" shape=\"none\" width=\"0\" height=\"0\"];\n" +
                  "  __start0 -> s0;\n}";
        return buffer;
    }
}

// Custom Triple class to hold three values
class Triple<K, V, S> {
    public K value1;
    public V value2;
    public S value3;

    public Triple(K value1, V value2, S value3) {
        this.value1 = value1;
        this.value2 = value2;
        this.value3 = value3;
    }
}